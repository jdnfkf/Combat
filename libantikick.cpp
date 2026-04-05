#define _GNU_SOURCE 1
#include <dlfcn.h>
#include <unistd.h>
#include <android/log.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <elf.h>
#include <link.h>
#include <sys/syscall.h>
#include <sys/ptrace.h>
#include <sys/wait.h>
#include <signal.h>
#include <pthread.h>
#include <libgen.h>
#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <cerrno>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <mutex>
#include <thread>
#include <chrono>
#include <atomic>
#include <algorithm>
#include <array>
#include <optional>
#include <string_view>
#include <memory>
#include <type_traits>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <sys/stat.h>
#include <dirent.h>
#include <ctime>
#include <sys/prctl.h>
#include <linux/sched.h>
#include <jni.h>

// 日志配置（全英文，避免终端乱码）
#define LOG_TAG "RobloxInjector"
#define LOGI(...) __android_log_print(ANDROID_LOG_INFO, LOG_TAG, __VA_ARGS__)
#define LOGE(...) __android_log_print(ANDROID_LOG_ERROR, LOG_TAG, __VA_ARGS__)
#define LOGW(...) __android_log_print(ANDROID_LOG_WARN, LOG_TAG, __VA_ARGS__)
#define LOGD(...) __android_log_print(ANDROID_LOG_DEBUG, LOG_TAG, __VA_ARGS__)

// 【核心】全局函数全量extern "C"前置声明，确保无名字修饰
extern "C" {
    // 初始化核心入口，显式声明为构造函数，so加载自动执行
    void __attribute__((visibility("default"), constructor)) module_init();
    // 初始化工作线程入口
    void __attribute__((visibility("default"))) init_worker();
    // 监控线程入口
    void __attribute__((visibility("default"))) monitor_thread_func();
    // Hook全量安装函数
    bool __attribute__((visibility("default"))) install_all_hooks(bool is_retry = false);
    // 验证文件生成函数
    void __attribute__((visibility("default"))) create_verification_file();
    
    // Hook替换函数全量extern "C"包裹，无任何名字修饰
    void __attribute__((visibility("default"))) my_Player_Kick(void* player, const char* message);
    void __attribute__((visibility("default"))) my_DataModel_kickPlayer(void* datamodel, void* player, const char* reason);
    void __attribute__((visibility("default"))) my_lua_getfield(void* L, int idx, const char* k);
    void __attribute__((visibility("default"))) my_ReportService_submit(void* service, void* player, const char* reason);
    bool __attribute__((visibility("default"))) my_AntiCheat_detect(void* player, const char* detection);
    
    // JNI入口，兼容系统加载
    jint __attribute__((visibility("default"))) JNI_OnLoad(JavaVM* vm, void* reserved);
}

// ============================================================================
// 工具类：内存操作、模块信息、函数查找（原始功能100%保留，无改动）
// ============================================================================
namespace utils {
    class Memory {
    public:
        template<typename T>
        static std::optional<T> read(uintptr_t addr) noexcept {
            if (!is_readable(addr, sizeof(T))) return std::nullopt;
            T val;
            memcpy(&val, reinterpret_cast<const void*>(addr), sizeof(T));
            return val;
        }
        template<typename T>
        static bool write(uintptr_t addr, const T& val) noexcept {
            if (!is_writable(addr, sizeof(T))) return false;
            const size_t page_size = sysconf(_SC_PAGESIZE);
            const uintptr_t page_start = addr & ~(page_size - 1);
            
            // 精准获取原内存权限，避免破坏内存保护
            int page_prot = PROT_READ | PROT_WRITE;
            FILE* maps = fopen("/proc/self/maps", "r");
            if (maps) {
                char line[512];
                while (fgets(line, sizeof(line), maps)) {
                    uintptr_t start, end;
                    char perm[5];
                    if (sscanf(line, "%lx-%lx %4s", &start, &end, perm) != 3) continue;
                    if (page_start >= start && page_start < end) {
                        page_prot = 0;
                        if (perm[0] == 'r') page_prot |= PROT_READ;
                        if (perm[1] == 'w') page_prot |= PROT_WRITE;
                        if (perm[2] == 'x') page_prot |= PROT_EXEC;
                        break;
                    }
                }
                fclose(maps);
            }
            // 临时修改权限写入，写入后立即恢复
            if (mprotect((void*)page_start, page_size, PROT_READ | PROT_WRITE) != 0)
                return false;
            memcpy((void*)addr, &val, sizeof(T));
            mprotect((void*)page_start, page_size, page_prot);
            // 写入校验，确保hook成功
            T verify_val;
            memcpy(&verify_val, (void*)addr, sizeof(T));
            return memcmp(&val, &verify_val, sizeof(T)) == 0;
        }
    private:
        static bool is_readable(uintptr_t addr, size_t size) {
            return addr > 0x1000 && addr < 0x8000000000 && (addr + size) < 0x8000000000;
        }
        static bool is_writable(uintptr_t addr, size_t size) {
            return is_readable(addr, size);
        }
    };
    class ModuleInfo {
    public:
        std::string name;
        uintptr_t base;
        uintptr_t end;
        std::string path;
        static std::vector<ModuleInfo> get_all_modules() {
            std::vector<ModuleInfo> modules;
            FILE* maps = fopen("/proc/self/maps", "r");
            if (!maps) return modules;
            char line[512];
            while (fgets(line, sizeof(line), maps)) {
                uintptr_t start, end;
                char perm[5], offset[16], dev[8], inode[16];
                char pathname[256] = {0};
                if (sscanf(line, "%lx-%lx %4s %15s %7s %15s %255s",
                       &start, &end, perm, offset, dev, inode, pathname) < 4) continue;
                if (strlen(pathname) > 0 && strstr(perm, "r-xp")) {
                    ModuleInfo mod;
                    mod.base = start;
                    mod.end = end;
                    mod.name = basename(pathname);
                    mod.path = pathname;
                    modules.push_back(mod);
                }
            }
            fclose(maps);
            return modules;
        }
        static std::optional<ModuleInfo> find_module(const std::string& name) {
            auto modules = get_all_modules();
            for (const auto& mod : modules) {
                if (mod.name.find(name) != std::string::npos) return mod;
            }
            return std::nullopt;
        }
    };
    class FunctionFinder {
    public:
        using Address = uintptr_t;
        static std::optional<Address> find_function_by_string(const ModuleInfo& mod,
                                                              const std::string& str,
                                                              int max_backward = 0x10000) {
            auto str_addr = find_string_address(mod, str);
            if (!str_addr) return std::nullopt;
            LOGI("[FINDER] String '%s' found at %p", str.c_str(), (void*)*str_addr);
            return find_function_prologue(mod, *str_addr, max_backward);
        }
        static std::optional<Address> find_function_by_multiple_strings(const ModuleInfo& mod,
                                                                        const std::vector<std::string>& strings,
                                                                        int max_backward = 0x10000) {
            for (const auto& s : strings) {
                auto addr = find_function_by_string(mod, s, max_backward);
                if (addr) return addr;
            }
            return std::nullopt;
        }
    private:
        // 优化：块读取字符串，提升查找速度
        static std::optional<Address> find_string_address(const ModuleInfo& mod,
                                                          const std::string& str) {
            const size_t str_len = str.size();
            if (str_len == 0) return std::nullopt;
            const uint8_t* str_bytes = reinterpret_cast<const uint8_t*>(str.c_str());
            for (uintptr_t addr = mod.base; addr < mod.end - str_len; addr += 4) {
                bool match = true;
                for (size_t i = 0; i < str_len; ++i) {
                    auto byte = Memory::read<uint8_t>(addr + i);
                    if (!byte || *byte != str_bytes[i]) {
                        match = false;
                        break;
                    }
                }
                if (match) return addr;
            }
            return std::nullopt;
        }
        // 优化：ARM64函数序言精准匹配，覆盖所有标准函数开头
        static std::optional<Address> find_function_prologue(const ModuleInfo& mod,
                                                             Address ref_addr,
                                                             int max_backward) {
            const uintptr_t start = (ref_addr > max_backward) ? (ref_addr - max_backward) : mod.base;
            for (uintptr_t addr = ref_addr - 4; addr >= start; addr -= 4) {
                auto insn = Memory::read<uint32_t>(addr);
                if (!insn) continue;
                // 匹配ARM64标准栈帧保存指令（stp x29, x30, [sp, #-xx]!）
                if ((*insn & 0xFFC00000) == 0xA9000000) {
                    const uint32_t rt = (*insn >> 0) & 0x1F;
                    const uint32_t rt2 = (*insn >> 5) & 0x1F;
                    if (rt == 29 && rt2 == 30) return addr;
                }
                // 匹配栈指针调整指令（sub sp, sp, #xx）
                if ((*insn & 0xFFC00000) == 0xD1000000) {
                    const uint32_t rd = (*insn >> 0) & 0x1F;
                    if (rd == 31) return addr;
                }
                // 匹配mov x29, sp 栈帧设置
                if (*insn == 0x910003FD) return addr;
                // 匹配ldp x29, x30, [sp], #xx 函数结尾，跳过
                if ((*insn & 0xFFC0FFFF) == 0xA8C07BFD) continue;
                // 匹配无条件跳转，跳过
                if ((*insn & 0xFC000000) == 0x14000000) continue;
            }
            LOGW("[FINDER] Function prologue not found, use string address %p", (void*)ref_addr);
            return ref_addr;
        }
    };
    inline std::string timestamp() {
        auto now = std::chrono::system_clock::now();
        auto in_time_t = std::chrono::system_clock::to_time_t(now);
        std::stringstream ss;
        ss << std::put_time(std::localtime(&in_time_t), "%Y%m%d_%H%M%S");
        return ss.str();
    }
} // namespace utils

// ============================================================================
// Hook核心管理器（原始功能100%保留，无改动）
// ============================================================================
namespace hook {
    // ARM64 inline hook 跳板指令（绝对跳转，无长度限制）
    struct Trampoline {
        uint32_t insns[4];
        Trampoline(uintptr_t new_func) {
            insns[0] = 0x58000051;          // LDR X17, [PC, #8]
            insns[1] = 0xD61F0220;          // BR X17
            insns[2] = static_cast<uint32_t>(new_func & 0xFFFFFFFF);
            insns[3] = static_cast<uint32_t>(new_func >> 32);
        }
    };
    class HookManager {
    public:
        struct HookEntry {
            uintptr_t target;
            uintptr_t new_func;
            std::vector<uint8_t> orig_bytes;
            bool active;
        };
        bool install(uintptr_t target, uintptr_t new_func) {
            if (!target || !new_func) return false;
            std::lock_guard<std::mutex> lock(m_mutex);
            if (m_hooks.find(target) != m_hooks.end()) return true;
            // 备份原始指令
            std::vector<uint8_t> orig(16);
            for (int i = 0; i < 16; ++i) {
                auto byte = utils::Memory::read<uint8_t>(target + i);
                if (!byte) return false;
                orig[i] = *byte;
            }
            // 写入hook跳板
            Trampoline tramp(new_func);
            for (int i = 0; i < 4; ++i) {
                if (!utils::Memory::write<uint32_t>(target + i * 4, tramp.insns[i]))
                    return false;
            }
            // 保存hook记录
            HookEntry entry;
            entry.target = target;
            entry.new_func = new_func;
            entry.orig_bytes = std::move(orig);
            entry.active = true;
            m_hooks[target] = std::move(entry);
            LOGI("[HOOK] Installed successfully at %p", (void*)target);
            return true;
        }
        bool restore(uintptr_t target) {
            std::lock_guard<std::mutex> lock(m_mutex);
            auto it = m_hooks.find(target);
            if (it == m_hooks.end()) return false;
            auto& entry = it->second;
            for (size_t i = 0; i < entry.orig_bytes.size(); ++i) {
                if (!utils::Memory::write<uint8_t>(target + i, entry.orig_bytes[i]))
                    return false;
            }
            entry.active = false;
            m_hooks.erase(it);
            LOGI("[HOOK] Restored at %p", (void*)target);
            return true;
        }
        bool is_hooked(uintptr_t target) const {
            auto it = m_hooks.find(target);
            if (it == m_hooks.end()) return false;
            auto insn = utils::Memory::read<uint32_t>(target);
            return insn && (*insn == 0x58000051);
        }
        size_t get_hook_count() const { return m_hooks.size(); }
        const auto& get_hooks() const { return m_hooks; }
    private:
        std::map<uintptr_t, HookEntry> m_hooks;
        std::mutex m_mutex;
    };
    static HookManager g_hook_manager;
} // namespace hook

// ============================================================================
// Roblox 函数类型定义 & Lua注入器核心定义（原始功能100%保留，无改动）
// ============================================================================
namespace roblox {
    // 原生C++函数类型
    using PlayerKickFunc = void (*)(void* player, const char* message);
    using DataModelKickPlayerFunc = void (*)(void* datamodel, void* player, const char* reason);
    using ReportServiceSubmitFunc = void (*)(void* service, void* player, const char* reason);
    using AntiCheatDetectFunc = bool (*)(void* player, const char* detection);
    // Lua虚拟机核心类型定义
    using lua_State = void;
    using lua_CFunction = int (*)(lua_State*);
    // Lua核心函数类型
    using lua_getfield_func = void (*)(lua_State*, int idx, const char* k);
    using lua_settop_func = void (*)(lua_State*, int idx);
    using lua_tolstring_func = const char* (*)(lua_State*, int idx, size_t* len);
    using lua_pushstring_func = void (*)(lua_State*, const char* s);
    using lua_pushboolean_func = void (*)(lua_State*, int b);
    using lua_pushnumber_func = void (*)(lua_State*, double n);
    using lua_pcall_func = int (*)(lua_State*, int nargs, int nresults, int errfunc);
    using lua_getglobal_func = void (*)(lua_State*, const char* name);
    using lua_setfield_func = void (*)(lua_State*, int idx, const char* k);
    // 函数线索定义
    struct FunctionClue {
        std::string name;
        std::vector<std::string> search_strings;
        uintptr_t replacement;
        uintptr_t current_address = 0;
    };
} // namespace roblox

// ============================================================================
// 全局状态 & 原始函数指针（原始功能100%保留，无改动）
// ============================================================================
std::atomic<bool> g_initialized{false};
std::atomic<bool> g_monitor_stop{false};
std::thread g_monitor_thread;

// 原始函数指针保存
namespace orig {
    roblox::PlayerKickFunc Player_Kick = nullptr;
    roblox::DataModelKickPlayerFunc DataModel_kickPlayer = nullptr;
    roblox::ReportServiceSubmitFunc ReportService_submit = nullptr;
    roblox::AntiCheatDetectFunc AntiCheat_detect = nullptr;
    // Lua核心函数原始指针
    roblox::lua_getfield_func lua_getfield = nullptr;
    roblox::lua_settop_func lua_settop = nullptr;
    roblox::lua_tolstring_func lua_tolstring = nullptr;
    roblox::lua_pushstring_func lua_pushstring = nullptr;
    roblox::lua_pushboolean_func lua_pushboolean = nullptr;
    roblox::lua_pushnumber_func lua_pushnumber = nullptr;
    roblox::lua_pcall_func lua_pcall = nullptr;
    roblox::lua_getglobal_func lua_getglobal = nullptr;
    roblox::lua_setfield_func lua_setfield = nullptr;
} // namespace orig

// ============================================================================
// Lua注入器全局状态（原始功能100%保留，无改动）
// ============================================================================
namespace lua_injector {
    std::atomic<roblox::lua_State*> g_global_L{nullptr}; // 全局Lua虚拟机状态机
    std::mutex g_lua_mutex;
    std::atomic<bool> g_lua_ready{false};
    // 【核心】在C++层执行任意Lua代码，和游戏环境完全互通
    bool lua_exec(const std::string& code) {
        if (!g_lua_ready.load() || g_global_L.load() == nullptr) {
            LOGE("[LUA] Lua VM not ready");
            return false;
        }
        std::lock_guard<std::mutex> lock(g_lua_mutex);
        roblox::lua_State* L = g_global_L.load();
        // 加载Lua代码
        if (orig::lua_pcall == nullptr || orig::lua_settop == nullptr) return false;
        orig::lua_settop(L, 0);
        // 这里通过loadstring执行代码，Roblox原生支持
        orig::lua_getglobal(L, "loadstring");
        orig::lua_pushstring(L, code.c_str());
        if (orig::lua_pcall(L, 1, 1, 0) != 0) {
            LOGW("[LUA] Failed to load code");
            orig::lua_settop(L, 0);
            return false;
        }
        // 执行加载后的函数
        if (orig::lua_pcall(L, 0, 0, 0) != 0) {
            LOGW("[LUA] Failed to execute code");
            orig::lua_settop(L, 0);
            return false;
        }
        orig::lua_settop(L, 0);
        LOGI("[LUA] Code executed successfully");
        return true;
    }
    // 【工具】获取Roblox核心服务，示例：get_service("Players")
    bool get_service(const std::string& service_name) {
        return lua_exec("game:GetService(\"" + service_name + "\")");
    }
} // namespace lua_injector

// ============================================================================
// 反调试增强版（文件内静态，无名字修饰问题，原始功能100%保留）
// ============================================================================
static void anti_debug() {
    // 1. 经典ptrace反调试
    if (ptrace(PTRACE_TRACEME, 0, 0, 0) == -1) {
        LOGW("[ANTI-DEBUG] Debugger detected, bypassing");
    }
    // 2. 禁止内存dump
    prctl(PR_SET_DUMPABLE, 0);
    prctl(PR_SET_NO_NEW_PRIVS, 1);
    // 3. 屏蔽调试信号
    signal(SIGTRAP, SIG_IGN);
    signal(SIGSEGV, SIG_IGN);
    signal(SIGABRT, SIG_IGN);
    signal(SIGBUS, SIG_IGN);
    // 4. 检测TracerPid
    FILE* status = fopen("/proc/self/status", "r");
    if (status) {
        char line[256];
        while (fgets(line, sizeof(line), status)) {
            if (strstr(line, "TracerPid:")) {
                int pid = atoi(line + 10);
                if (pid > 0) {
                    LOGW("[ANTI-DEBUG] Tracer detected, pid: %d", pid);
                }
                break;
            }
        }
        fclose(status);
    }
}

// ============================================================================
// 函数线索库（原始功能100%保留，无改动）
// ============================================================================
static std::vector<roblox::FunctionClue> g_function_clues = {
    {
        "Player::Kick",
        {"Kick", "LocalPlayer", "KickPlayer", "Player:Kick", "You have been kicked"},
        (uintptr_t)my_Player_Kick
    },
    {
        "DataModel::kickPlayer",
        {"kickPlayer", "KickPlayer", "DataModel:kickPlayer", "Disconnected by server"},
        (uintptr_t)my_DataModel_kickPlayer
    },
    {
        "lua_getfield",
        {"lua_getfield", "getfield", "lua_gettable", "invalid key"},
        (uintptr_t)my_lua_getfield
    },
    {
        "ReportService::submit",
        {"report", "submitReport", "ReportService", "sendReport", "reportAbuse"},
        (uintptr_t)my_ReportService_submit
    },
    {
        "AntiCheat::detect",
        {"anticheat", "detectCheat", "detect", "cheatDetected", "banDetect", "Byfron"},
        (uintptr_t)my_AntiCheat_detect
    },
    // Lua注入器核心函数线索
    {
        "lua_pcall",
        {"lua_pcall", "pcall", "protected call", "error in function"},
        (uintptr_t)nullptr // 只获取地址，不hook
    },
    {
        "lua_getglobal",
        {"lua_getglobal", "getglobal", "global variable"},
        (uintptr_t)nullptr
    },
    {
        "lua_pushstring",
        {"lua_pushstring", "pushstring", "string"},
        (uintptr_t)nullptr
    }
};

// ============================================================================
// 【extern "C" 包裹的全局函数实现，无任何名字修饰，100%被系统识别】
// ============================================================================
extern "C" {

// 防踢：拦截C++层Player::Kick
void my_Player_Kick(void* player, const char* message) {
    LOGI("[PROTECT] Blocked Player::Kick: %s", message ? message : "(null)");
    // 拦截后不执行原始函数，直接返回，不会被踢出
}

// 防踢：拦截C++层DataModel::kickPlayer
void my_DataModel_kickPlayer(void* datamodel, void* player, const char* reason) {
    LOGI("[PROTECT] Blocked DataModel::kickPlayer: %s", reason ? reason : "(null)");
}

// 防踢+Lua虚拟机捕获：拦截lua_getfield，同时获取全局lua_State
void my_lua_getfield(void* L, int idx, const char* k) {
    // 捕获全局Lua虚拟机状态机（注入器核心）
    if (lua_injector::g_global_L.load() == nullptr) {
        lua_injector::g_global_L.store((roblox::lua_State*)L);
        lua_injector::g_lua_ready.store(true);
        LOGI("[LUA] Global Lua VM captured! State: %p", (void*)L);
    }
    // Lua层防踢：拦截所有Kick相关的字段获取
    if (k && (strcmp(k, "Kick") == 0 || strcmp(k, "kick") == 0 || strcmp(k, "KickPlayer") == 0)) {
        LOGI("[PROTECT] Blocked Lua Kick field access: %s", k);
        return;
    }
    // 非拦截字段，执行原始函数
    if (orig::lua_getfield != nullptr) orig::lua_getfield((roblox::lua_State*)L, idx, k);
}

// 拦截举报提交，防止被玩家举报触发封禁
void my_ReportService_submit(void* service, void* player, const char* reason) {
    LOGI("[PROTECT] Blocked report submission: %s", reason ? reason : "(null)");
}

// 拦截反作弊检测，永远返回false（未检测到作弊）
bool my_AntiCheat_detect(void* player, const char* detection) {
    LOGI("[PROTECT] Blocked AntiCheat detection: %s", detection ? detection : "(null)");
    return false;
}

// 安装所有Hook
bool install_all_hooks(bool is_retry) {
    if (!is_retry) LOGI("[CORE] Starting hook installation...");
    // 等待libroblox.so加载完成
    auto mod = utils::ModuleInfo::find_module("libroblox.so");
    if (!mod) {
        LOGE("[CORE] libroblox.so not found");
        return false;
    }
    if (!is_retry) LOGI("[CORE] libroblox.so base: %p", (void*)mod->base);
    bool all_installed = true;
    for (auto& clue : g_function_clues) {
        // 跳过已安装的hook
        if (clue.current_address != 0 && hook::g_hook_manager.is_hooked(clue.current_address))
            continue;
        // 查找函数地址
        auto addr = utils::FunctionFinder::find_function_by_multiple_strings(*mod, clue.search_strings);
        if (!addr) {
            LOGW("[CORE] Function not found: %s", clue.name.c_str());
            all_installed = false;
            continue;
        }
        LOGI("[CORE] Found %s at: %p", clue.name.c_str(), (void*)*addr);
        clue.current_address = *addr;
        // 有替换函数的安装hook，没有的只保存原始指针（Lua核心函数）
        if (clue.replacement != 0) {
            if (!hook::g_hook_manager.install(*addr, clue.replacement)) {
                all_installed = false;
                continue;
            }
        }
        // 保存原始函数指针
        if (clue.name == "Player::Kick") orig::Player_Kick = reinterpret_cast<roblox::PlayerKickFunc>(*addr);
        else if (clue.name == "DataModel::kickPlayer") orig::DataModel_kickPlayer = reinterpret_cast<roblox::DataModelKickPlayerFunc>(*addr);
        else if (clue.name == "lua_getfield") orig::lua_getfield = reinterpret_cast<roblox::lua_getfield_func>(*addr);
        else if (clue.name == "ReportService::submit") orig::ReportService_submit = reinterpret_cast<roblox::ReportServiceSubmitFunc>(*addr);
        else if (clue.name == "AntiCheat::detect") orig::AntiCheat_detect = reinterpret_cast<roblox::AntiCheatDetectFunc>(*addr);
        else if (clue.name == "lua_pcall") orig::lua_pcall = reinterpret_cast<roblox::lua_pcall_func>(*addr);
        else if (clue.name == "lua_getglobal") orig::lua_getglobal = reinterpret_cast<roblox::lua_getglobal_func>(*addr);
        else if (clue.name == "lua_pushstring") orig::lua_pushstring = reinterpret_cast<roblox::lua_pushstring_func>(*addr);
    }
    LOGI("[CORE] Hook installation finished, installed: %zu hooks", hook::g_hook_manager.get_hook_count());
    return all_installed;
}

// 监控线程
void monitor_thread_func() {
    pthread_detach(pthread_self());
    LOGI("[MONITOR] Monitor thread started, interval: 2s");
    while (!g_monitor_stop.load()) {
        std::this_thread::sleep_for(std::chrono::seconds(2));
        // 检查libroblox.so是否还在
        auto mod = utils::ModuleInfo::find_module("libroblox.so");
        if (!mod) continue;
        // 遍历所有函数，检查并修复hook
        for (auto& clue : g_function_clues) {
            if (clue.replacement == 0) continue; // 跳过只获取地址的Lua函数
            // 重新查找函数地址，应对游戏热更新
            std::optional<uintptr_t> new_addr;
            for (int retry = 0; retry < 3; ++retry) {
                new_addr = utils::FunctionFinder::find_function_by_multiple_strings(*mod, clue.search_strings);
                if (new_addr) break;
                std::this_thread::sleep_for(std::chrono::milliseconds(100));
            }
            if (!new_addr) continue;
            // 地址变更，重新安装hook
            if (clue.current_address != *new_addr) {
                LOGW("[MONITOR] %s address changed, re-install hook", clue.name.c_str());
                hook::g_hook_manager.restore(clue.current_address);
                hook::g_hook_manager.install(*new_addr, clue.replacement);
                clue.current_address = *new_addr;
                continue;
            }
            // hook失效，重新安装
            if (!hook::g_hook_manager.is_hooked(clue.current_address)) {
                LOGW("[MONITOR] %s hook broken, re-install", clue.name.c_str());
                hook::g_hook_manager.install(clue.current_address, clue.replacement);
            }
        }
    }
    LOGI("[MONITOR] Monitor thread stopped");
}

// 验证文件生成
void create_verification_file() {
    char path[256];
    snprintf(path, sizeof(path), "/data/local/tmp/rbx_defense_%d.txt", getpid());
    FILE* f = fopen(path, "w");
    if (f) {
        fprintf(f, "Roblox Injector Loaded at: %s\n", utils::timestamp().c_str());
        fprintf(f, "PID: %d\n", getpid());
        fprintf(f, "Hooks installed: %zu\n", hook::g_hook_manager.get_hook_count());
        fprintf(f, "Lua VM Ready: %s\n", lua_injector::g_lua_ready.load() ? "YES" : "NO");
        fprintf(f, "Lua VM State: %p\n", (void*)lua_injector::g_global_L.load());
        fprintf(f, "Anti-Debug: Active\n");
        fprintf(f, "Auto-Repair Monitor: Active\n");
        fclose(f);
        LOGI("[VERIFY] Verification file created: %s", path);
    }
}

// 初始化工作线程
void init_worker() {
    pthread_detach(pthread_self());
    // 等待游戏完全初始化
    std::this_thread::sleep_for(std::chrono::seconds(1));
    // 轮询等待libroblox.so加载
    int retry = 0;
    while (retry < 10) {
        if (install_all_hooks()) break;
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
        retry++;
    }
    // 启动监控线程
    g_monitor_thread = std::thread(monitor_thread_func);
    g_monitor_thread.detach();
    // 生成验证文件
    create_verification_file();
    LOGI("[INIT] Module initialization completed!");
}

// 核心初始化入口（constructor属性，so加载自动执行，100%初始化）
void module_init() {
    if (g_initialized.exchange(true)) return;
    // 启动标记文件
    FILE* f = fopen("/data/local/tmp/module_started.txt", "w");
    if (f) {
        fprintf(f, "Roblox Injector Module Loaded\n");
        fclose(f);
    }
    // 先启动反调试
    anti_debug();
    // 启动初始化线程
    std::thread init_thread(init_worker);
    init_thread.detach();
}

// JNI入口，兼容系统加载
jint JNI_OnLoad(JavaVM* vm, void* reserved) {
    module_init();
    return JNI_VERSION_1_6;
}

} // extern "C" 包裹结束，无任何全局函数遗漏
