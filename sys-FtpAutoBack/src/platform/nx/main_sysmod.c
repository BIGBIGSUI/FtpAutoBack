// main_sysmod.c - 整理后的头文件包含和函数前向声明
// 从根目录main_sysmod.c文件中提取并整理

// ========== 项目头文件 ==========
#include "ftpsrv.h"
#include <ftpsrv_vfs.h>
#include "utils.h"
#include "log/log.h"
#include "log/backuplog.h"
#include "custom_commands.h"
#include "vfs_nx.h"
#include "vfs/vfs_nx_save.h"

// ========== 系统头文件 ==========
// 标准C库
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>
#include <errno.h>
#include <ctype.h>
#include <fcntl.h>

// 系统相关
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/iosupport.h>
#include <dirent.h>

// 网络相关
#include <arpa/inet.h>
#include <netdb.h>

// Nintendo Switch相关
#include <switch.h>
#include <switch/services/bsd.h>
#include <switch/services/nifm.h>

// 第三方库
#include <minIni.h>
#include <curl/curl.h>
#include <zlib.h>
#include <libxml/parser.h>
#include <libxml/tree.h>

// ========== 宏定义 ==========
// NTP相关定义
#define UNIX_OFFSET 2208988800L
#define NTP_DEFAULT_SERVER "ntp.ntsc.ac.cn"
#define NTP_DEFAULT_PORT "123"
#define NTP_DEFAULT_TIMEOUT 5
#define NTP_FLAGS 0x1B // LI=0, VN=3, Mode=3

// 网络缓冲区定义
#define TCP_TX_BUF_SIZE (1024 * 4)
#define TCP_RX_BUF_SIZE (1024 * 4)
#define TCP_TX_BUF_SIZE_MAX (1024 * 64)
#define TCP_RX_BUF_SIZE_MAX (1024 * 64)
#define UDP_TX_BUF_SIZE (0)
#define UDP_RX_BUF_SIZE (0)
#define SB_EFFICIENCY (1)

#define ALIGN_MSS(v) ((((v) + 1500 - 1) / 1500) * 1500)

#define SOCKET_TMEM_SIZE \
    ((((( \
      ALIGN_MSS(TCP_TX_BUF_SIZE_MAX ? TCP_TX_BUF_SIZE_MAX : TCP_TX_BUF_SIZE) \
    + ALIGN_MSS(TCP_RX_BUF_SIZE_MAX ? TCP_RX_BUF_SIZE_MAX : TCP_RX_BUF_SIZE)) \
    + (UDP_TX_BUF_SIZE ? ALIGN_MSS(UDP_TX_BUF_SIZE) : 0)) \
    + (UDP_RX_BUF_SIZE ? ALIGN_MSS(UDP_RX_BUF_SIZE) : 0)) \
    + 0xFFF) &~ 0xFFF) \
    * SB_EFFICIENCY

#define NUMBER_OF_SOCKETS (2)
#define HEAP_SIZE (512 * 1024)  // 512KB堆内存 (优化: 1MB -> 512KB)

// ========== 结构体定义 ==========
// NTP数据包结构体
typedef struct {
    uint8_t flags;
    uint8_t stratum;
    uint8_t poll;
    uint8_t precision;
    uint32_t root_delay;
    uint32_t root_dispersion;
    uint8_t referenceID[4];
    uint32_t ref_ts_secs;
    uint32_t ref_ts_frac;
    uint32_t origin_ts_secs;
    uint32_t origin_ts_frac;
    uint32_t recv_ts_secs;
    uint32_t recv_ts_frac;
    uint32_t transmit_ts_secs;
    uint32_t transmit_ts_frac;
} ntp_packet;

// WebDAV响应数据结构体
struct WebDAVResponseData {
    char* data;
    size_t size;
};

// WebDAV上传数据结构体
struct WebDAVUploadData {
    FsFile* file_handle;
    u64 total_uploaded;
    u64 file_size;
    char debug_buf[128];
};

// 存档文件信息结构体
struct SaveFileInfo {
    char path[FS_MAX_PATH];
    char filename[256];
    time_t timestamp;
    int sequence;  // 序列号字段，用于带序列号的存档格式
};



// ========== 全局变量声明 ==========
// 配置相关全局变量
static const char* INI_PATH = "/config/ftpsrv/config.ini";
static const char* LOG_PATH = "/config/ftpsrv/log.txt";
static const char* AUTOBACK_DIR_PATH = "/AutoBack";
static struct FtpSrvConfig g_ftpsrv_config = {0};
static bool g_led_enabled = false;
static bool g_back_led_enabled = false;
static bool g_backup_notify_enabled = false;
static volatile bool g_should_exit = false;
static u32 g_webdav_tcp_buffer_max_size = 0;

// 用户信息相关全局变量
static AccountUid g_current_game_user_uid = {0};
static char g_current_game_user_name[33] = {0};

// 游戏文件夹创建相关全局变量
static char sanitized_name[0x200] = {0};
static char tid_str[17] = {0};
static char* folder_name = NULL;

// 游戏TID跟踪
static u64 g_previous_game_tid = 0;

// WebDAV配置结构体
static struct {
    bool enabled;
    char origin[256];
    char basepath[64];
    char username[64];
    char password[64];
} webdav_config = {0};

// maxback配置参数
static int g_maxback = 0;

// 线程相关全局变量
static Thread g_ftp_service_thread;                                    // FTP服务线程对象
static alignas(0x1000) char g_ftp_thread_stack[16 * 1024];           // FTP线程栈内存 (16KB)

static Thread g_auto_backup_service_thread;                           // 自动备份服务线程对象  
static alignas(0x1000) char g_auto_backup_thread_stack[64 * 1024];   // 自动备份线程栈内存 (64KB)


// 系统相关全局变量
extern u32 __nx_applet_type;
extern u32 __nx_fs_num_sessions;

// 堆内存相关
static alignas(0x1000) u8 g_heap_mem[HEAP_SIZE];
static alignas(0x1000) u8 SOCKET_TRANSFER_MEM[SOCKET_TMEM_SIZE * NUMBER_OF_SOCKETS];

// 网络状态相关全局变量
static bool g_bsd_initialized = false;
static bool g_standard_socket_initialized = false;
static bool g_webdav_handshake_in_progress = false;

// ========== 函数前向声明 ==========

// ========== 系统初始化与生命周期管理 ==========
void __libnx_init_time(void);
void __libnx_initheap(void);
void __appInit(void);
void __appExit(void);

// ========== 基础配置初始化 ==========
static bool initialize_log(void);
static bool initialize_ftp_server_config(void);
static void initialize_FS_VFS(void);
static bool initialize_AutoBack_DIR(void);
static bool initialize_Curl(void);
static bool initialize_WebDAV(void);
static bool initialize_AutoBack_Thread(void);
static bool initialize_Ftp_Thread(void);
static void Clean_Ftp_Thread(void);
static void Clean_AutoBack_Thread(void);



// ========== 网络服务管理 ==========
// 网络初始化与清理
static Result initialize_bsd_sockets(void);
static void cleanup_bsd_sockets(void);
static Result initialize_standard_sockets(void);
static void cleanup_standard_sockets(void);

// 网络状态与时间同步
static bool is_network_available(void);
static time_t get_ntp_time(void);

// 服务模式切换
Result switch_to_webdav_mode(void);
Result switch_to_ftp_mode(void);

// ========== 核心服务线程 ==========
static void ftp_thread(void* arg);
static void auto_backup_thread(void* arg);

// ========== FTP服务回调函数 ==========
static void ftp_log_callback(enum FTP_API_LOG_TYPE type, const char* msg);
static void ftp_progress_callback(void);



// ========== 存档备份管理 ==========
// 游戏信息获取与处理
static Result get_current_tid(u64* tid);
static bool update_user_uid_name(void);
static u64 Get_Current_Commit_Id(u64 current_tid);
static void create_game_folder(u64 tid);
static void generate_save_archive(u64 tid);

// 存档文件管理
static time_t parse_timestamp_from_filename(const char* filename, int* sequence);
static int compare_save_files(const void* a, const void* b);
static void manage_backup_count(const char* username, const char* game_folder);
static void manage_webdav_backup_count(const char* username, const char* game_folder);

// 文件流处理
static Result stream_zip_to_sdcard(struct mmz_Data* mz, FsFileSystem* sdmc_fs, const char* output_path);

// ========== WebDAV云存储服务 ==========
// WebDAV连接与认证
static bool webdav_handshake(void);
static bool create_webdav_directory(const char* dir_path);

// WebDAV数据传输回调
static size_t webdav_response_write_callback(void* ptr, size_t size, size_t nmemb, void* user_data);
static size_t webdav_upload_read_callback(void* ptr, size_t size, size_t nmemb, void* user_data);

// WebDAV文件操作
static void get_latest_webdav_timestamp_and_sequence(const char* username, const char* folder_name, 
                                                     char* latest_timestamp, size_t timestamp_size, 
                                                     int* sequence_num);
static Result stream_zip_to_webdav(const char* local_zip_path, u64 tid, AccountUid user_uid, const char* username);

// ========== 用户界面与通知 ==========
// LED效果控制
void enableBreathingEffect(HidsysUniquePadId unique_pad_id);
void disableBreathingEffect(HidsysUniquePadId unique_pad_id);
void enableHeartbeatEffect(HidsysUniquePadId unique_pad_id);
void disableHeartbeatEffect(HidsysUniquePadId unique_pad_id);
bool Show_Back_LED(void);
void Close_Back_LED(void);

// Ultrahand通知系统
static void create_ultrahand_notification(const char* message, int priority);
static Result createDirectory(const char* path);
static Result createTextFile(const char* path, const char* content);

// ========== 工具函数 ==========
// 字符串处理
static void sanitize_filename(char* filename);
static bool custom_strptime(const char* time_str, const char* format, struct tm* tm_info);
static void url_decode(char* str);

// 系统工具
static u32 socketSelectVersion(void);

// ========== 主函数实现 ==========
/**
 * 主函数 - FTP自动备份系统模块入口点
 * 
 * 功能说明：
 * 1. 初始化配置参数（从config.ini读取FTP服务器、登录、网络等配置）
 * 2. 设置自定义挂载点（支持最多10个用户自定义的挂载路径）
 * 3. 启动FTP服务器线程和自动备份监控线程
 * 4. 处理系统退出信号，确保资源正确释放
 * 
 * 配置文件路径：/config/ftpsrv/config.ini
 * 支持的功能：FTP服务器、WebDAV上传、自动存档备份、LED指示灯控制
 */
int main(void) {

    // ====初始化FTP的部分====
    // 初始化日志，根据配置文件决定是否开启日志
    initialize_log();

    // 初始化FTP配置文件内容，如果初始化失败则EXIT
    if (!initialize_ftp_server_config()) return EXIT_FAILURE;

    // 初始化虚拟文件系统
    initialize_FS_VFS();

    // 初始化FTP服务线程
    bool ftp_thread_state = initialize_Ftp_Thread();
    // ====初始化FTP完成====

    // ====初始化自动备份的部分====
    // 从配置文件读取自动备份开关状态
    bool auto_backup_enabled = ini_getbool("Backup-Basic Settings", "auto_backup", 1, INI_PATH);

    // 初始化用户目录（只有开启自动备份才初始化）
    bool auto_backup_dir_init = false;
    if (auto_backup_enabled) auto_backup_dir_init = initialize_AutoBack_DIR();
    else log_file_write("未启用自动备份功能，跳过初始化用户目录");

    // 只有初始化用户目录成功才执行
    // 先初始化curl，成功则初始化WebDAV
    // 无论curl初始化是否成功，都启动自动备份线程,和备份日志
    bool curl_init_rc = false;
    bool auto_backup_thread_state = false;
    if (auto_backup_dir_init) {
        curl_init_rc = initialize_Curl();
        if (!curl_init_rc) webdav_config.enabled = false;
        else initialize_WebDAV();
        backuplog_init();
        auto_backup_thread_state = initialize_AutoBack_Thread();
    } else log_file_write("初始化用户列表失败，禁止启用备份功能！");
    // ====初始化自动备份完成====
    
    // 主线程等待，保持程序运行
    while (!g_should_exit) {
        svcSleepThread(1000000000); // 1秒延迟
    }
    
    // 退出时停止所有服务线程
    g_should_exit = true;
    
    // 清理线程
    if (ftp_thread_state) Clean_Ftp_Thread();
    if (auto_backup_thread_state) Clean_AutoBack_Thread();
    
    if (curl_init_rc) {
        curl_global_cleanup();
        log_file_write("成功清理curl服务！");
    }
}

// ========== 系统初始化与生命周期管理 ==========

// 堆内存初始化函数
void __libnx_initheap(void) {
    extern char* fake_heap_start;
    extern char* fake_heap_end;

    // Configure the newlib heap - Enable 512KB heap space for libcurl use
    fake_heap_start = (char*)g_heap_mem;
    fake_heap_end   = (char*)g_heap_mem + HEAP_SIZE;
    
    // 添加调试日志
    char debug_buf[256];
    snprintf(debug_buf, sizeof(debug_buf), "Heap initialized: start=0x%lx, end=0x%lx, size=%d bytes", 
             (u64)fake_heap_start, (u64)fake_heap_end, HEAP_SIZE);
    log_file_write(debug_buf);
}

// 应用初始化函数
void __appInit(void) {
    Result rc;

    if (R_FAILED(rc = smInitialize()))
        diagAbortWithResult(rc);

    rc = setsysInitialize();
    if (R_SUCCEEDED(rc)) {
        SetSysFirmwareVersion fw;
        rc = setsysGetFirmwareVersion(&fw);
        if (R_SUCCEEDED(rc))
            hosversionSet(MAKEHOSVERSION(fw.major, fw.minor, fw.micro));
        setsysExit();
    }

    if (R_FAILED(rc = timeInitialize()))
        diagAbortWithResult(rc);
    if (R_FAILED(rc = fsInitialize()))
        diagAbortWithResult(rc);
    if (R_FAILED(rc = fsdev_wrapMountSdmc()))
        diagAbortWithResult(rc);
    if (R_FAILED(rc = accountInitialize(AccountServiceType_System)))
        diagAbortWithResult(rc);
    if (R_FAILED(rc = ncmInitialize()))
        diagAbortWithResult(rc);
    if (R_FAILED(rc = setInitialize()))
        diagAbortWithResult(rc);
    if (R_FAILED(rc = nifmInitialize(NifmServiceType_User)))
        diagAbortWithResult(rc);

    hidsysInitialize();
    __libnx_init_time();
    
    // 默认初始化BSD套接字（FTP服务优先）
    if (R_FAILED(rc = initialize_bsd_sockets())) {
        diagAbortWithResult(rc);
    }
}

// 应用退出函数
void __appExit(void) {
    // 清理所有套接字资源
    cleanup_bsd_sockets();
    cleanup_standard_sockets();
    
    vfs_nx_exit();
    log_file_exit();
    hidsysExit();
    nifmExit();
    setExit();
    ncmExit();
    accountExit();
    fsdev_wrapUnmountAll();
    fsExit();
    timeExit();
    smExit();
}



// ========== 基础配置初始化 ==========

/**
 * @brief 初始化日志系统
 * @return true 日志初始化成功，false 日志初始化失败
 */
static bool initialize_log(void) {

    // 调试用的日志，可配置开启
    bool log_enabled = ini_getbool("Common", "log", 0, INI_PATH);
    if (log_enabled) {
        log_file_init(LOG_PATH, "日志系统初始化完毕！");
        log_file_fwrite("备份记录初始化完成");
    }
    return log_enabled;
}

/**
 * @brief 初始化FTP服务器基础信息配置
 * @return true 配置初始化成功，false 配置初始化失败
 */
static bool initialize_ftp_server_config(void) {

    g_ftpsrv_config.custom_command = CUSTOM_COMMANDS;
    g_ftpsrv_config.custom_command_count = CUSTOM_COMMANDS_SIZE;
    g_ftpsrv_config.log_callback = ftp_log_callback;
    g_ftpsrv_config.progress_callback = ftp_progress_callback;
    g_ftpsrv_config.anon = ini_getbool("Ftp-Login", "anon", 0, INI_PATH);
    g_ftpsrv_config.port = ini_getl("Ftp-Network", "port", 21, INI_PATH);
    g_ftpsrv_config.timeout = ini_getl("Ftp-Network", "timeout", 0, INI_PATH);
    g_ftpsrv_config.use_localtime = ini_getbool("Ftp-Basic Settings", "use_localtime", 0, INI_PATH);

    int user_len = ini_gets("Ftp-Login", "user", "", g_ftpsrv_config.user, sizeof(g_ftpsrv_config.user), INI_PATH);
    int pass_len = ini_gets("Ftp-Login", "pass", "", g_ftpsrv_config.pass, sizeof(g_ftpsrv_config.pass), INI_PATH);

    if (!user_len && !pass_len && !g_ftpsrv_config.anon) {
        log_file_write("未设置账户与密码，且未开启匿名登录！");
        return false;
    }

    // 放别的地方不合适，临时放这里吧
    g_led_enabled = ini_getbool("Ftp-Basic Settings", "led", 1, INI_PATH);

    return true;
}

/**
 * @brief 初始化系统虚拟文件系统（VFS）
 * @return true VFS初始化成功，false VFS初始化失败
 */
static void initialize_FS_VFS(void) {

    /**
    * mount_devices                 是否开启挂载设备
    * mount_bis                     是否挂载Bis文件系统
    * save_writable                 是否开启存档写入权限
    * skip_ascii_convert            是否跳过ASCII转换
    */

    bool mount_devices = ini_getbool("Ftp-Basic Settings", "mount_devices", 1, INI_PATH);
    bool mount_bis = ini_getbool("Ftp-Basic Settings", "mount_bis", 0, INI_PATH);
    bool save_writable = ini_getbool("Ftp-Basic Settings", "save_writable", 0, INI_PATH);
    bool skip_ascii_convert = ini_getbool("Common", "skip_ascii_convert", 0, INI_PATH);
    

    // 自定义虚拟挂载，最多10项
    CustomMountPoint custom_mounts[10] = {0};  
    int custom_mount_count = 0;
    if (mount_devices) {
        for (int i = 1; i <= 10; i++) {
            char name_key[14];
            char path_key[14];
            char temp_name[30] = {0};
            char temp_path[64] = {0};
            
            // 构造键名
            snprintf(name_key, sizeof(name_key), "custom_name%d", i);
            snprintf(path_key, sizeof(path_key), "custom_path%d", i);
            
            // 读取显示名称和挂载路径
            ini_gets("Ftp-Custom Mount Point", name_key, "", temp_name, sizeof(temp_name), INI_PATH);
            ini_gets("Ftp-Custom Mount Point", path_key, "", temp_path, sizeof(temp_path), INI_PATH);
            
            // 如果两个值都不为空，则添加到数组中
            if (strlen(temp_name) > 0 && strlen(temp_path) > 0) {
                strncpy(custom_mounts[custom_mount_count].display_name, temp_name, sizeof(custom_mounts[custom_mount_count].display_name) - 1);
                strncpy(custom_mounts[custom_mount_count].mount_path, temp_path, sizeof(custom_mounts[custom_mount_count].mount_path) - 1);
                custom_mount_count++;
            } else break;
        }
    }

    // 初始化虚拟文件系统
    vfs_nx_init(NULL, mount_devices, save_writable, mount_bis, skip_ascii_convert, custom_mounts);
    log_file_write("虚拟文件系统初始化完毕！");

}

/**
 * @brief 初始化自动备份目录
 * @return true 目录初始化成功，false 目录初始化失败
 */
static bool initialize_AutoBack_DIR(void) {

    // 暂时没别的地方放了，临时放这里吧。
    g_maxback = ini_getl("Backup-Basic Settings", "maxback", 0, INI_PATH);  // 最大备份数量
    g_back_led_enabled = ini_getbool("Backup-Basic Settings", "backup_led", 0, INI_PATH);  // LED提示
    g_backup_notify_enabled = ini_getbool("Backup-Basic Settings", "backup_notify", 0, INI_PATH);  // 弹窗通知

    // 创建AutoBack文件夹
    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
    if (sdmc_fs != NULL) {
        Result rc = fsFsCreateDirectory(sdmc_fs, AUTOBACK_DIR_PATH);
        if (R_SUCCEEDED(rc)) {
            log_file_write("AutoBack文件夹创建成功！");
        } else if (rc == 0x402) { // FSERROR_PATH_ALREADY_EXISTS
            log_file_write("AutoBack文件夹已存在！");
        } else {
            char buf[128];
            snprintf(buf, sizeof(buf), "创建AutoBack文件夹失败：0x%x", rc);
            log_file_write(buf);
            return false;
        }

    } else {
        log_file_write("挂载SD卡文件系统失败！");
        return false;
    }

    // 遍历全部用户名，在AutoBack文件夹内生成所有用户名文件夹
    AccountUid user_ids[ACC_USER_LIST_SIZE] = {0};
    s32 total_users = 0;
    // 获取全部用户数量
    Result account_rc = accountGetUserCount(&total_users);
    if (R_FAILED(account_rc) || total_users <= 0) {
        char buf[128];
        snprintf(buf, sizeof(buf), "获取用户数量失败：0x%x", account_rc);
        log_file_write(buf);
        return false;
    }
    
    // 列出所有用户
    account_rc = accountListAllUsers(user_ids, ACC_USER_LIST_SIZE, &total_users);
    if (R_FAILED(account_rc)) {
        char buf[128];
        snprintf(buf, sizeof(buf), "列出所有用户失败：0x%x", account_rc);
        log_file_write(buf);
        return false;
    }

    int success_count = 0;
    // 遍历所有用户
    for (s32 i = 0; i < total_users; i++) {
        AccountProfile profile = {0};                   // 账户配置文件
        AccountUserData user_data = {0};                // 账户用户数据
        AccountProfileBase profile_base = {0};          // 账户配置文件基本信息

        account_rc = accountGetProfile(&profile, user_ids[i]);
        if (R_FAILED(account_rc)) {
            char buf[128];
            snprintf(buf, sizeof(buf), "获取用户配置文件失败：0x%x", account_rc);
            log_file_write(buf);
            continue;
        }

        account_rc = accountProfileGet(&profile, &user_data, &profile_base);
        if (R_FAILED(account_rc)) {
            char buf[128];
            snprintf(buf, sizeof(buf), "获取用户配置文件基本信息失败：0x%x", account_rc);
            log_file_write(buf);
            accountProfileClose(&profile);
            continue;
        }

        // AccountProfileBase 中的 nickname（昵称）字段长度为 32 个字符，再加上一个空终止符
        char username[33] = {0}; 
        strncpy(username, profile_base.nickname, sizeof(username) - 1);

        // 获取用户名文件夹路径 /AutoBack/用户名
        char user_folder_path[128] = {0};
        snprintf(user_folder_path, sizeof(user_folder_path), "%s/%s", AUTOBACK_DIR_PATH, username);

        // 创建用户名文件夹
        Result mkdir_rc = fsFsCreateDirectory(sdmc_fs, user_folder_path);
        if (R_SUCCEEDED(mkdir_rc)) {
            char log_buf[512] = {0};
            snprintf(log_buf, sizeof(log_buf), "成功创建用户文件夹: %s", user_folder_path);
            log_file_write(log_buf);
            success_count++;
        } else if (mkdir_rc == 0x402) { // FSERROR_PATH_ALREADY_EXISTS
            char log_buf[512] = {0};
            snprintf(log_buf, sizeof(log_buf), "用户文件夹已存在: %s", user_folder_path);
            log_file_write(log_buf);
            success_count++;
        } else {
            char log_buf[512] = {0};
            snprintf(log_buf, sizeof(log_buf), "创建用户文件夹 %s 失败：0x%x", user_folder_path, mkdir_rc);
            log_file_write(log_buf);
        }
        // 关闭用户配置文件句柄
        accountProfileClose(&profile);
    }

    char buf[128];
    snprintf(buf, sizeof(buf), "共 %d 个用户，成功创建 %d 个，失败 %d 个！", total_users, success_count, total_users - success_count);
    log_file_write(buf);

    // 检查是否全部创建失败，若失败则返回false
    if (success_count == 0) return false;
    else return true;

}


/**
 * @brief 初始化Curl WebDAV
 * 
 * @return true 初始化成功，false 初始化失败
 */
static bool initialize_Curl(void) {

    // 初始化CURL库 
    CURLcode curl_result = curl_global_init(CURL_GLOBAL_ALL);
    if (curl_result != CURLE_OK) {
        char curl_error_buf[128];
        snprintf(curl_error_buf, sizeof(curl_error_buf), "初始化CURL库失败: %s ,停止初始化WebDAV服务", curl_easy_strerror(curl_result));
        log_file_write(curl_error_buf);
        return false;
    } 

    log_file_write("CURL库初始化成功！");

    return true;

}

static bool initialize_WebDAV(void) {
    // 读取WebDAV配置 
    webdav_config.enabled = ini_getbool("Backup-WebDAV", "WebDAV_enabled", 0, INI_PATH);

    int user_len = ini_gets("Backup-WebDAV", "username", "", webdav_config.username, sizeof(webdav_config.username), INI_PATH);
    int pass_len = ini_gets("Backup-WebDAV", "password", "", webdav_config.password, sizeof(webdav_config.password), INI_PATH);

    if (!user_len && !pass_len) {
        webdav_config.enabled = false;
        log_file_write("未设置账户与密码！");
        return false;
    }

    if (!webdav_config.enabled) {
        log_file_write("WebDAV服务已禁用，");
        return false;
    }

    ini_gets("Backup-WebDAV", "origin", "", webdav_config.origin, sizeof(webdav_config.origin), INI_PATH);
    ini_gets("Backup-WebDAV", "basepath", "", webdav_config.basepath, sizeof(webdav_config.basepath), INI_PATH);

    // 读取高速上传配置
    bool high_speed = ini_getbool("Backup-WebDAV", "high_speed", 0, INI_PATH);

    // 根据high_speed值动态设置缓冲区大小
    g_webdav_tcp_buffer_max_size = high_speed ? 0x20000 : 0x8000;  // true=128KB, false=32KB

    char webdav_log_buf[128];
    snprintf(webdav_log_buf, sizeof(webdav_log_buf), "WebDAV服务已启用。地址: %s, 路径: %s, 用户: %s", webdav_config.origin, webdav_config.basepath, webdav_config.username);
    log_file_write(webdav_log_buf);

    return true;
   
}

/**
 * @brief 初始化FTP服务器线程
 * 
 * @return true 线程初始化成功，false 线程初始化失败
 */
static bool initialize_Ftp_Thread(void) {
    
    log_file_write("开始创建FTP服务线程...");
    
    // 根据sysFtpAutoBack.json配置，线程优先级必须在24-63范围内，使用与主线程相同的优先级49
    Result ftp_thread_rc = threadCreate(&g_ftp_service_thread, ftp_thread, NULL, g_ftp_thread_stack, sizeof(g_ftp_thread_stack), 49, 3);
    if (R_FAILED(ftp_thread_rc)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "创建线程失败，错误码: 0x%x", ftp_thread_rc);
        log_file_write(debug_buf);
        // 添加更多调试信息
        snprintf(debug_buf, sizeof(debug_buf), "线程栈地址: 0x%lx, 线程入口函数: 0x%lx", (u64)&g_ftp_thread_stack, (u64)ftp_thread);
        log_file_write(debug_buf);
        return false;
    }

    log_file_write("FTP服务线程创建成功,准备启动线程...");
    ftp_thread_rc = threadStart(&g_ftp_service_thread);
    if (R_FAILED(ftp_thread_rc)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "启动线程失败，错误码: 0x%x", ftp_thread_rc);
        log_file_write(debug_buf);
        threadClose(&g_ftp_service_thread);
        return false;
    }

    return true;

}

/**
 * @brief 初始化自动备份线程
 * 
 * @return true 线程初始化成功，false 线程初始化失败
 */
static bool initialize_AutoBack_Thread(void) {

    log_file_write("开始创建自动备份线程...");
    Result auto_backup_thread_rc = threadCreate(&g_auto_backup_service_thread, auto_backup_thread, NULL, 
                                                g_auto_backup_thread_stack, sizeof(g_auto_backup_thread_stack), 49, 3);
   
    if (R_FAILED(auto_backup_thread_rc)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "创建线程失败，错误码: 0x%x", auto_backup_thread_rc);
        log_file_write(debug_buf);
        // 添加更多调试信息
        snprintf(debug_buf, sizeof(debug_buf), "线程栈地址: 0x%lx, 线程入口函数: 0x%lx", (u64)&g_auto_backup_thread_stack, (u64)auto_backup_thread);
        log_file_write(debug_buf);
        return false;
    }

    log_file_write("自动备份线程创建成功，准备启动线程...");
    auto_backup_thread_rc = threadStart(&g_auto_backup_service_thread);
    if (R_FAILED(auto_backup_thread_rc)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "启动线程失败，错误码: 0x%x", auto_backup_thread_rc);
        log_file_write(debug_buf);
        threadClose(&g_auto_backup_service_thread);
        return false;
    }
    
    log_file_write("自动备份线程启动成功");

    return true;

}

/**
 * @brief 清理FTP服务线程
 * 
 * @param ftp_thread_state FTP服务线程状态
 */
static void Clean_Ftp_Thread(void) {

    // 无限等待阻塞，需要添加超时机制，暂时没添加
    threadWaitForExit(&g_ftp_service_thread);
    Result close_result = threadClose(&g_ftp_service_thread);
    if (R_FAILED(close_result)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "关闭线程失败，错误码: 0x%x", close_result);
        log_file_write(debug_buf);
        return;
    }

    log_file_write("FTP服务线程清理成功");
    
}

/**
 * @brief 清理自动备份线程
 * 
 * @param auto_backup_thread_state 自动备份线程状态
 */
static void Clean_AutoBack_Thread(void) {

    // 无限等待阻塞，需要添加超时机制，暂时没添加
    threadWaitForExit(&g_auto_backup_service_thread);
    Result close_result = threadClose(&g_auto_backup_service_thread);
    if (R_FAILED(close_result)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "关闭线程失败，错误码: 0x%x", close_result);
        log_file_write(debug_buf);
        return;
    }

    log_file_write("自动备份线程清理成功");
}



// ========== 网络服务管理 ==========

// 网络初始化与清理
static Result initialize_bsd_sockets(void) {
    if (g_bsd_initialized) {
        return 0; // Already initialized
    }
    
    const SocketInitConfig socket_config = {
        .tcp_tx_buf_size     = TCP_TX_BUF_SIZE,
        .tcp_rx_buf_size     = TCP_RX_BUF_SIZE,
        .tcp_tx_buf_max_size = TCP_TX_BUF_SIZE_MAX,
        .tcp_rx_buf_max_size = TCP_RX_BUF_SIZE_MAX,
        .udp_tx_buf_size     = UDP_TX_BUF_SIZE,
        .udp_rx_buf_size     = UDP_RX_BUF_SIZE,
        .sb_efficiency       = SB_EFFICIENCY,
        .num_bsd_sessions    = 1,
        .bsd_service_type    = BsdServiceType_Auto,
    };

    const BsdInitConfig bsd_config = {
        .version             = socketSelectVersion(),
        .tmem_buffer         = SOCKET_TRANSFER_MEM,
        .tmem_buffer_size    = sizeof(SOCKET_TRANSFER_MEM),
        .tcp_tx_buf_size     = socket_config.tcp_tx_buf_size,
        .tcp_rx_buf_size     = socket_config.tcp_rx_buf_size,
        .tcp_tx_buf_max_size = socket_config.tcp_tx_buf_max_size,
        .tcp_rx_buf_max_size = socket_config.tcp_rx_buf_max_size,
        .udp_tx_buf_size     = socket_config.udp_tx_buf_size,
        .udp_rx_buf_size     = socket_config.udp_rx_buf_size,
        .sb_efficiency       = socket_config.sb_efficiency,
    };
    
    Result rc = bsdInitialize(&bsd_config, socket_config.num_bsd_sessions, socket_config.bsd_service_type);
    if (R_SUCCEEDED(rc)) {
        g_bsd_initialized = true;
        log_file_write("BSD sockets initialized successfully");
    } else {
        char error_buf[256];
        snprintf(error_buf, sizeof(error_buf), "Failed to initialize BSD sockets: 0x%x", rc);
        log_file_write(error_buf);
    }
    
    return rc;
}

static void cleanup_bsd_sockets(void) {
    if (g_bsd_initialized) {
        bsdExit();
        g_bsd_initialized = false;
        log_file_write("BSD sockets cleaned up");
    }
}

static Result initialize_standard_sockets(void) {
    if (g_standard_socket_initialized) {
        return 0; // 已经初始化
    }
    
    // 运行时初始化socket配置，使用动态缓冲区大小
    SocketInitConfig webdav_socket_config = {
        .tcp_tx_buf_size = 0x800,                               // 2KB (保持)
        .tcp_rx_buf_size = 0x800,                               // 2KB (保持)
        .tcp_tx_buf_max_size = g_webdav_tcp_buffer_max_size,   // 根据high_speed值动态设置缓冲区大小，true=128KB, false=32KB
        .tcp_rx_buf_max_size = g_webdav_tcp_buffer_max_size,   // 根据high_speed值动态设置缓冲区大小，true=128KB, false=32KB
        .udp_tx_buf_size = 0x1000,                              // 4KB (优化: 32KB -> 4KB)
        .udp_rx_buf_size = 0x1000,                              // 4KB (优化: 32KB -> 4KB)
        .sb_efficiency = 1,
    };
    
    Result rc = socketInitialize(&webdav_socket_config);
    if (R_SUCCEEDED(rc)) {
        g_standard_socket_initialized = true;
        log_file_write("Standard sockets initialized successfully");
    } else {
        char error_buf[256];
        snprintf(error_buf, sizeof(error_buf), "Failed to initialize standard sockets: 0x%x", rc);
        log_file_write(error_buf);
    }
    
    return rc;
}

static void cleanup_standard_sockets(void) {
    if (g_standard_socket_initialized) {
        socketExit();
        g_standard_socket_initialized = false;
        log_file_write("标准套接字已清理！");
    }
}

// 网络状态与时间同步
static bool is_network_available(void) {
    // 增强的网络状态检查，增加容错性
    NifmNetworkProfileData profile;
    Result rc = nifmGetCurrentNetworkProfile(&profile);
    
    if (R_SUCCEEDED(rc)) {
        // 进一步检查网络配置文件的有效性
        if (profile.ip_setting_data.ip_address_setting.is_automatic || 
            (profile.ip_setting_data.ip_address_setting.current_addr.addr[0] != 0 ||
             profile.ip_setting_data.ip_address_setting.current_addr.addr[1] != 0 ||
             profile.ip_setting_data.ip_address_setting.current_addr.addr[2] != 0 ||
             profile.ip_setting_data.ip_address_setting.current_addr.addr[3] != 0)) {
            return true;
        }
    }
    
    // 如果主要检查失败，尝试备用检查方法
    // 检查NIFM服务状态
    NifmInternetConnectionType connection_type;
    u32 wifi_strength;
    NifmInternetConnectionStatus connection_status;
    
    Result backup_rc = nifmGetInternetConnectionStatus(&connection_type, &wifi_strength, &connection_status);
    if (R_SUCCEEDED(backup_rc)) {
        // 如果能获取到连接状态，认为网络基本可用
        return (connection_status == NifmInternetConnectionStatus_Connected);
    }
    
    // 最后的容错机制：如果所有检查都失败，但BSD套接字已初始化，
    // 则认为网络可能可用（避免过于严格的检查导致误判）
    if (g_bsd_initialized) {
        return true;  // 容错返回true，让上层逻辑继续
    }
    
    return false;
}

static time_t get_ntp_time(void) {
    int server_sock = -1;
    struct addrinfo hints, *servinfo = NULL;
    int status;
    ntp_packet packet;
    bool time_retrieved = false;
    
    log_file_write("准备访问NPT服务器，同步时间");
    
    // 检查网络是否可用
    if (!is_network_available()) {
        log_file_write("网络不可用，无法同步时间");
        return 0;
    }
    log_file_write("网络可用，准备同步时间");
    
    // 确保标准套接字已初始化
    if (!g_standard_socket_initialized) {
        log_file_write("标准套接字未初始化，正在初始化...");
        if (R_FAILED(initialize_standard_sockets())) {
            log_file_write("初始化标准套接字失败");
            return 0;
        }
        log_file_write("标准套接字初始化成功");
    } else {
        log_file_write("标准套接字已初始化");
    }
    
    // 设置地址信息
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;
    
    // 获取NTP服务器地址
    log_file_write("正在解析NTP服务器地址...");
    if ((status = getaddrinfo(NTP_DEFAULT_SERVER, NTP_DEFAULT_PORT, &hints, &servinfo)) != 0) {
        char error_buf[256];
        snprintf(error_buf, sizeof(error_buf), "NTP getaddrinfo失败: %s", gai_strerror(status));
        log_file_write(error_buf);
        return 0;
    }
    log_file_write("NTP服务器地址解析成功");
    
    // 尝试连接到NTP服务器
    struct addrinfo* ap;
    for (ap = servinfo; ap != NULL; ap = ap->ai_next) {
        log_file_write("正在尝试创建套接字...");
        server_sock = socket(ap->ai_family, ap->ai_socktype, ap->ai_protocol);
        if (server_sock == -1) {
            char sock_error[64];
            snprintf(sock_error, sizeof(sock_error), "创建套接字失败: %d", errno);
            log_file_write(sock_error);
            continue;
        }
        log_file_write("套接字创建成功");
        
        // 设置超时
        struct timeval tv = {.tv_sec = NTP_DEFAULT_TIMEOUT, .tv_usec = 0};
        if (setsockopt(server_sock, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv)) < 0) {
            char opt_error[64];
            snprintf(opt_error, sizeof(opt_error), "设置SO_RCVTIMEO失败: %d", errno);
            log_file_write(opt_error);
            close(server_sock);
            server_sock = -1;
            continue;
        }
        
        if (setsockopt(server_sock, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv)) < 0) {
            char opt_error[64];
            snprintf(opt_error, sizeof(opt_error), "设置SO_SNDTIMEO失败: %d", errno);
            log_file_write(opt_error);
            close(server_sock);
            server_sock = -1;
            continue;
        }
        log_file_write("套接字选项设置成功");

        // 构造标准NTP请求
        memset(&packet, 0, sizeof(packet));
        packet.flags = NTP_FLAGS;
        
        // 发送NTP请求
        log_file_write("正在发送NTP请求...");
        ssize_t sent_bytes = sendto(server_sock, &packet, sizeof(packet), 0, ap->ai_addr, ap->ai_addrlen);
        if (sent_bytes == -1) {
            char send_error[64];
            snprintf(send_error, sizeof(send_error), "发送NTP请求失败: %d", errno);
            log_file_write(send_error);
            close(server_sock);
            server_sock = -1;
            continue;
        }
        char send_info[64];
        snprintf(send_info, sizeof(send_info), "已发送NTP请求: %zd 字节", sent_bytes);
        log_file_write(send_info);
        
        // 接收NTP响应
        log_file_write("正在接收NTP响应...");
        struct sockaddr_storage server_addr;
        socklen_t server_addr_len = sizeof(server_addr);
        ssize_t recv_bytes = recvfrom(server_sock, &packet, sizeof(packet), 0, (struct sockaddr*)&server_addr, &server_addr_len);
        if (recv_bytes == -1) {
            char recv_error[64];
            snprintf(recv_error, sizeof(recv_error), "接收NTP响应失败: %d", errno);
            log_file_write(recv_error);
            close(server_sock);
            server_sock = -1;
            continue;
        }
        char recv_info[64];
        snprintf(recv_info, sizeof(recv_info), "已接收NTP响应: %zd 字节", recv_bytes);
        log_file_write(recv_info);
        
        time_retrieved = true;
        break;
    }
    
    if (servinfo) {
        freeaddrinfo(servinfo);
    }
    
    if (!time_retrieved) {
        log_file_write("所有尝试后仍未获取到NTP时间");
        if (server_sock != -1) {
            close(server_sock);
        }
        return 0;
    }
    
    close(server_sock);
    
    // 转换NTP时间戳为Unix时间戳
    packet.recv_ts_secs = ntohl(packet.recv_ts_secs);
    time_t ntp_time = packet.recv_ts_secs - UNIX_OFFSET;
    
    // 记录成功获取NTP时间
    char time_buf[128];
    struct tm* tm_info = localtime(&ntp_time);
    strftime(time_buf, sizeof(time_buf), "已成功获取NTP时间: %Y-%m-%d %H:%M:%S", tm_info);
    log_file_write(time_buf);
    
    return ntp_time;
}

// 服务模式切换
Result switch_to_webdav_mode(void) {
    log_file_write("Switching to WebDAV mode...");
    
    // 清理BSD套接字
    cleanup_bsd_sockets();
    
    // 初始化标准套接字
    Result rc = initialize_standard_sockets();
    if (R_SUCCEEDED(rc)) {
        g_webdav_handshake_in_progress = true;
        log_file_write("Successfully switched to WebDAV mode");
    }
    
    return rc;
}

Result switch_to_ftp_mode(void) {
    log_file_write("准备切换到FTP模式");
    
    // 清理标准套接字
    cleanup_standard_sockets();
    
    // 添加额外延迟确保资源完全释放
    svcSleepThread(50000000LL); // 50ms
    
    // 初始化BSD套接字
    Result rc = initialize_bsd_sockets();
    if (R_FAILED(rc)) {
        // BSD套接字初始化失败，也需要重置状态防止死锁
        char error_buf[128];
        snprintf(error_buf, sizeof(error_buf), "初始化BSD套接字失败,无法切换到FTP模式: 0x%x", rc);
        log_file_write(error_buf);
        log_file_write("BSD套接字初始化失败，已强制重置WebDAV握手状态以防止死锁");
        g_webdav_handshake_in_progress = false;
        return rc;
    }

    log_file_write("初始化BSD套接字成功！");
    // 确保状态完全同步
    svcSleepThread(50000000LL); // 额外50ms确保状态同步

    // 初始化完成，需要验证套接字
    bool socket_ready = false;
    int retry_count = 0;
    const int max_retries = 5;
    const int retry_delay_ms = 200; // 200ms延迟
    
    // 重试5次验证套接字状态，每次200ms延迟
    while (!socket_ready && retry_count < max_retries) {
        if (g_bsd_initialized && is_network_available()) {
            socket_ready = true;
            break;
        }
        
        retry_count++;
        char retry_log[128];
        snprintf(retry_log, sizeof(retry_log), 
                    "正在验证套接字与网络是否就绪，第%d/%d次重试", 
                    retry_count, max_retries);
        log_file_write(retry_log);
        
        // 等待后重试
        svcSleepThread(retry_delay_ms * 1000000LL);
    }
    
    // 重置握手状态
    g_webdav_handshake_in_progress = false;

    if (socket_ready) {
        log_file_write("套接字验证成功，WebDAV握手状态已重置");
        log_file_write("自动备份线程可以重新开始TID监控");
    } else {
        char warning_log[128];
        snprintf(warning_log, sizeof(warning_log), "套接字验证失败，已重试%d次，强制重置WebDAV状态以防止死锁", max_retries);
        log_file_write(warning_log);
        log_file_write("已强制重置WebDAV握手状态，自动备份线程将继续监控TID");
        log_file_write("注意：网络连接可能不稳定，但是TID监控将继续进行");
    }
    
    return rc;
}

// ========== 核心服务线程 ==========
// FTP服务线程函数
static void ftp_thread(void* arg) {
    int timeout = -1;
    if (g_ftpsrv_config.timeout) {
        timeout = 1000 * g_ftpsrv_config.timeout;
    }
    
    while (!g_should_exit) {
        ftpsrv_init(&g_ftpsrv_config);
        while (!g_should_exit) {
            if (ftpsrv_loop(timeout) != FTP_API_LOOP_ERROR_OK) {
                svcSleepThread(1000000000);
                break;
            }
        }
        ftpsrv_exit();
    }
}

// 自动备份存档线程函数
static void auto_backup_thread(void* arg) {
    // 当前的id
    u64 current_tid = 0;
    
    // 添加commitid变化检测变量
    u64 previous_commit_id = 0;    //之前的
    u64 current_commit_id = 0;      //当前的
    int commit_change_count = 0;
    
    // 确保BSD套接字模式，保证TID监控100%运行
    log_file_write("自动备份线程启动 - 需确保用 BSD 套接字模式来对 TID 监控");
    Result force_switch_rc = switch_to_ftp_mode();
    // 额外等待确保状态稳定
    svcSleepThread(100000000LL); // 100ms

    if (R_FAILED(force_switch_rc)) {
        log_file_write("第一次启动BSD套接字失败，尝试第二次！");
        if (R_SUCCEEDED(initialize_bsd_sockets())) log_file_write("第二次启动BSD套接字成功！");
        else log_file_write("第二次启动BSD套接字失败！");
        g_webdav_handshake_in_progress = false;
        log_file_write("强制重置WebDAV握手状态！");
    }

    // 额外等待确保状态稳定
    svcSleepThread(100000000LL); // 100ms

    // 线程首次启动时获取一次当前正在运行的游戏TID
    get_current_tid(&current_tid);
    g_previous_game_tid = current_tid;
    
    // 直接死循环监控TID变化
    while (!g_should_exit) {

        // 3种值，1正确的游戏TID，2未进入游戏时的TID，3获取失败TID=0
        get_current_tid(&current_tid);

        // 当进入游戏的时候(当前TID不是0且不是桌面的TID)
        if (current_tid != 0 && current_tid != 0x0100000000001000ULL) {
            // 更新全局的UID和NAME
            update_user_uid_name();

            // 检查当前用户UID是否有有效
            if (accountUidIsValid(&g_current_game_user_uid)) {
                // 获取当前游戏的CommitID
                current_commit_id = Get_Current_Commit_Id(current_tid);
                // 当CommitID发生变化时
                if (previous_commit_id != 0 && current_commit_id != 0 && current_commit_id != previous_commit_id) {
                    commit_change_count++;
                    log_file_fwrite("CommitID 从 %016lX 变为 %016lX, 改变次数: %d", 
                                    previous_commit_id, current_commit_id, commit_change_count);
                }
                // 记录当前CommitID为下一次比较的基础
                previous_commit_id = current_commit_id;
            }

        }

        // 当TID发生了变化，且不是从桌面进入别的应用，而是从别的应用切换到别的应用(包括切换到桌面)
        if (current_tid != 0 && current_tid != g_previous_game_tid ) {
            log_file_fwrite("检测到新的 TID: %016lX，旧的 TID: %016lX", current_tid, g_previous_game_tid);
            // 检测是否是有效的游戏ID
            if (g_previous_game_tid != 0x0100000000001000ULL && (g_previous_game_tid & 0xFFFF000000000000ULL) == 0x0100000000000000ULL) {
                // 检查commitid变化次数
                if (commit_change_count >= 1) {
                    // 检测到存档变化时发送Ultrahand通知
                    create_ultrahand_notification("存档已变化，开始备份", 1);

                    // 开启呼吸灯
                    bool led_enabled = Show_Back_LED();

                    // 生成存档
                    generate_save_archive(g_previous_game_tid);
                    log_file_fwrite("创建游戏 %016lX 的存档备份 - CommitID 变化次数: %d", g_previous_game_tid, commit_change_count);

                    // 关闭LED效果作为完成提示，只有在成功开启时才关闭
                    if (led_enabled) Close_Back_LED();

                } 
                else {
                    log_file_fwrite("跳过游戏 %016lX 的存档备份 - CommitID 未变化 (变化次数: %d)", g_previous_game_tid, commit_change_count);
                }
                
            }
            // 重置相关变量，从头开始
            g_previous_game_tid = current_tid;
            previous_commit_id = 0;
            current_commit_id = 0;
            commit_change_count = 0;
            log_file_fwrite("重置游戏 %016lX 的 CommitID 跟踪变量", current_tid);

        }

        // 如果检测到WebDAV握手正在进行，等待其完成
        if (g_webdav_handshake_in_progress) {
            log_file_write("检测到 WebDAV 握手正在进行，等待完成...");
            int wait_count = 0;
            while (g_webdav_handshake_in_progress && wait_count < 10) { // 最多等待10秒
                svcSleepThread(1000000000); // 1秒延迟
                wait_count++;
            }
            if (g_webdav_handshake_in_progress) log_file_write("警告: WebDAV 握手超时，强制检查套接字状态");
        }
        
        // 无论是否正在进行WebDAV握手，都检查套接字状态
        if (!g_bsd_initialized || !is_network_available()) {
            Result init_rc = initialize_bsd_sockets();
            if (R_FAILED(init_rc)) log_file_fwrite("警告: 初始化 BSD 套接字失败: 0x%x", init_rc);
            else log_file_write("警告: BSD 套接字未初始化，已重新初始化！");
        }
        
        // 添加延迟避免CPU占用过高
        svcSleepThread(1000000000); // 1秒延迟

    }
}

// ========== FTP服务回调函数 ==========
// FTP日志回调函数
static void ftp_log_callback(enum FTP_API_LOG_TYPE type, const char* msg) {
    log_file_write(msg);
    if (g_led_enabled) {
        led_flash();
    }
}

// FTP进度回调函数
static void ftp_progress_callback(void) {
    if (g_led_enabled) {
        led_flash();
    }
}



// ========== 存档备份管理 ==========
// 游戏信息获取与处理
static Result get_current_tid(u64* tid) {
    Result rc;
    
    if (R_FAILED(rc = pmdmntInitialize())) {
        return rc;
    }
    
    if (R_FAILED(rc = pminfoInitialize())) {
        pmdmntExit();
        return rc;
    }

    u64 pid;

    // 获取当前应用的PID与进程ID
    rc = pmdmntGetApplicationProcessId(&pid);
    if (R_SUCCEEDED(rc)) rc = pminfoGetProgramId(tid, pid);

    // 统一处理rc的值
    if (rc == 0x20f) {
        *tid = 0x0100000000001000ULL; // QLAUNCH_TID
        rc = 0; // 设置为成功状态，确保日志能被记录
    } else if (R_FAILED(rc)) {
        *tid = 0; // 只有在真正失败时才设置为0
        log_file_fwrite("警告: 获取当前应用的PID或者TID失败，错误码: 0x%x", rc);
    }

    pminfoExit();
    pmdmntExit();
    return rc;
}

/**
 * 更新当前游戏用户的UID和用户名
 * 
 * 功能说明：
 * 1. 获取最后打开的用户UID
 * 2. 获取用户配置文件和昵称
 * 3. 验证用户名有效性，提供后备方案
 * 4. 更新全局变量 g_current_game_user_uid 和 g_current_game_user_name
 * 
 * 返回值：
 * - true: 成功获取用户信息（包括使用后备方案）
 * - false: 完全失败，无法获取任何用户信息
 */
static bool update_user_uid_name(void) {
    // 清空全局变量
    memset(&g_current_game_user_uid, 0, sizeof(g_current_game_user_uid));
    memset(g_current_game_user_name, 0, sizeof(g_current_game_user_name));
    // 尝试获取用户账户信息
    Result user_rc = accountGetLastOpenedUser(&g_current_game_user_uid);
    if (R_FAILED(user_rc)) {
        log_file_fwrite("[ERROR]获取最后打开的用户信息失败: 0x%x", user_rc);
        // 清空用户信息并设置安全的默认值
        // 确保UID为空(0)，用户名设置为"Unknown_User"
        memset(&g_current_game_user_uid, 0, sizeof(g_current_game_user_uid));
        strcpy(g_current_game_user_name, "Unknown_User");
        return false; // 完全失败
    }

    // 尝试获取用户配置文件
    AccountProfile profile;
    memset(&profile, 0, sizeof(profile));
    user_rc = accountGetProfile(&profile, g_current_game_user_uid);
    if (R_FAILED(user_rc)) {
        log_file_fwrite("[ERROR]获取用户配置文件信息失败: 0x%x", user_rc);
        // 确保UID有效后再使用
        if (g_current_game_user_uid.uid[0] != 0 || g_current_game_user_uid.uid[1] != 0) {
            snprintf(g_current_game_user_name, sizeof(g_current_game_user_name), 
                        "User_%016lX", g_current_game_user_uid.uid[0]);
        } else strcpy(g_current_game_user_name, "Unknown_User");
        return true; 
    }
    
    // 尝试获取用户配置文件基础信息
    AccountProfileBase profilebase;
    memset(&profilebase, 0, sizeof(profilebase));
    user_rc = accountProfileGet(&profile, NULL, &profilebase);
    if (R_FAILED(user_rc)) {
        log_file_fwrite("[ERROR]获取用户配置文件基础信息失败: 0x%x", user_rc);
        // 确保UID有效后再使用
        if (g_current_game_user_uid.uid[0] != 0 || g_current_game_user_uid.uid[1] != 0) {
            snprintf(g_current_game_user_name, sizeof(g_current_game_user_name), 
                        "User_%016lX", g_current_game_user_uid.uid[0]);
        } else {
            strcpy(g_current_game_user_name, "Unknown_User");
        }
        // 确保profile被正确关闭
        accountProfileClose(&profile);
        return true; 
    }

    // 安全地复制用户名并进行验证
    memset(g_current_game_user_name, 0, sizeof(g_current_game_user_name));
    // 检查nickname是否有效且不为空
    if (profilebase.nickname[0] != '\0' && strnlen(profilebase.nickname, sizeof(profilebase.nickname)) > 0) {
        // 安全复制，确保不会溢出
        size_t copy_len = strnlen(profilebase.nickname, sizeof(profilebase.nickname));
        if (copy_len >= sizeof(g_current_game_user_name)) copy_len = sizeof(g_current_game_user_name) - 1;
        // 复制到全局变量   
        memcpy(g_current_game_user_name, profilebase.nickname, copy_len);
        g_current_game_user_name[copy_len] = '\0';
        
        // 验证用户名是否包含有效字符
        bool has_valid_chars = false;
        for (size_t i = 0; i < copy_len; i++) {
            char c = g_current_game_user_name[i];
            if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) {
                has_valid_chars = true;
                break;
            }
        }
        
        // 如果用户名没有有效字符，使用UID作为后备
        if (!has_valid_chars) {
            snprintf(g_current_game_user_name, sizeof(g_current_game_user_name), 
                        "User_%016lX", g_current_game_user_uid.uid[0]);
        }
    } else {
        // 如果nickname为空或无效，使用UID作为用户名
        snprintf(g_current_game_user_name, sizeof(g_current_game_user_name), 
                    "User_%016lX", g_current_game_user_uid.uid[0]);
    }

    // 确保profile被正确关闭
    accountProfileClose(&profile);
    return true; // 成功获取用户信息（包括后备方案）
}

// 获取指定游戏和用户的当前CommitID
// 参数: application_id - 游戏的TID, uid - 用户ID
// 返回: 成功时返回CommitID，失败时返回0
static u64 Get_Current_Commit_Id(u64 current_tid) {
    
    // 构建查询过滤器
    FsSaveDataFilter filter = {0};
    filter.filter_by_save_data_type = true;
    filter.attr.save_data_type = FsSaveDataType_Account;
    filter.filter_by_user_id = true;
    filter.attr.uid = g_current_game_user_uid;
    filter.filter_by_application_id = true;
    filter.attr.application_id = current_tid;
    // 初始化当前CommitID为0
    u64 current_commit_id = 0;

    // 初始化读取器
    FsSaveDataInfoReader reader;
    Result rc = fsOpenSaveDataInfoReaderWithFilter(&reader, FsSaveDataSpaceId_User, &filter);
    if (R_FAILED(rc)) {
        log_file_fwrite("打开游戏 %016lX 的 SaveDataInfoReader 失败: 0x%x", current_tid, rc);
        return 0;
    }

    // 读取SaveDataInfo
    FsSaveDataInfo info;
    s64 total;
    rc = fsSaveDataInfoReaderRead(&reader, &info, 1, &total);
    if (R_FAILED(rc) || total <= 0) {
        log_file_fwrite("读取游戏 %016lX 的 SaveID 失败: 0x%x", current_tid, rc);
        fsSaveDataInfoReaderClose(&reader);
        return 0;
    }

    // 确保这个游戏发生了改变的时候输出日志
    if (current_tid != g_previous_game_tid){
        log_file_fwrite("游戏 %016lX 用户 %s 的 SaveID: %016lX", current_tid, 
                        g_current_game_user_name[0] ? g_current_game_user_name : "Unknown", info.save_data_id);
    }

    // 使用saveid获取存档额外数据
    FsSaveDataExtraData extra_data;
    memset(&extra_data, 0, sizeof(extra_data));
    Result extra_rc = fsReadSaveDataFileSystemExtraData(&extra_data, sizeof(FsSaveDataExtraData), info.save_data_id);
    if (R_FAILED(extra_rc)) {
        log_file_fwrite("读取游戏 %016lX 的 SaveDataExtraData 失败: 0x%x", current_tid, extra_rc);
        fsSaveDataInfoReaderClose(&reader);
        return 0;
    }

    // 从额外数据中提取CommitID
    current_commit_id = extra_data.commit_id;
    // 确保reader被正确关闭
    fsSaveDataInfoReaderClose(&reader);

    // 确保这个游戏发生了改变的时候输出日志
    if (current_tid != g_previous_game_tid){
        log_file_fwrite("读取游戏 %016lX 的 CommitID ：%016lX", current_tid, current_commit_id);
    }

    return current_commit_id;

}

static void create_game_folder(u64 tid) {
    if (tid == 0) return;
    
    // 获取游戏名称
    NcmContentId content_id = {0};
    struct AppName app_name = {0};
    get_app_en_name(tid, &content_id, &app_name);

    // 清理游戏名称中的非法字符
    memset(sanitized_name, 0, sizeof(sanitized_name));
    if (strlen(app_name.str) > 0) {
        strncpy(sanitized_name, app_name.str, sizeof(sanitized_name) - 1);
        sanitize_filename(sanitized_name);
    }
    
    folder_name = sanitized_name;
    memset(tid_str, 0, sizeof(tid_str));
    if (strlen(sanitized_name) == 0) {
        snprintf(tid_str, sizeof(tid_str), "%016lX", tid);
        folder_name = tid_str;
    }

    log_file_fwrite("准备创建游戏文件夹 %s", folder_name);
    
    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
    if (sdmc_fs == NULL) {
        log_file_write("警告: 无法获取 SD 卡文件系统，无法创建游戏文件夹");
        return;
    }
    
    // 遍历全部用户名，在autoback文件夹内生成游戏名称文件夹
    AccountUid user_ids[ACC_USER_LIST_SIZE] = {0};
    s32 total_users = 0;
    Result account_rc = accountGetUserCount(&total_users);
    if (R_SUCCEEDED(account_rc) && total_users > 0) {
        account_rc = accountListAllUsers(user_ids, ACC_USER_LIST_SIZE, &total_users);
        if (R_SUCCEEDED(account_rc)) {
            for (s32 i = 0; i < total_users; i++) {
                AccountProfile profile = {0};
                AccountUserData user_data = {0};
                AccountProfileBase profile_base = {0};
                
                account_rc = accountGetProfile(&profile, user_ids[i]);
                if (R_SUCCEEDED(account_rc)) {
                    account_rc = accountProfileGet(&profile, &user_data, &profile_base);
                    if (R_SUCCEEDED(account_rc)) {
                        char username[33] = {0}; // AccountProfileBase nickname is 32 chars + null terminator
                        
                        // 安全地复制和验证用户名
                        if (profile_base.nickname[0] != '\0') {
                            strncpy(username, profile_base.nickname, sizeof(username) - 1);
                            username[sizeof(username) - 1] = '\0';
                            
                            // 清理用户名中的特殊字符
                            sanitize_filename(username);
                            
                            // 验证清理后的用户名是否有效
                            if (strlen(username) == 0) {
                                snprintf(username, sizeof(username), "User_%016lX", user_ids[i].uid[0]);
                            }
                        } else {
                            // 如果nickname为空，使用UID作为用户名
                            snprintf(username, sizeof(username), "User_%016lX", user_ids[i].uid[0]);
                        }
                        
                        // 创建游戏名称文件夹路径，添加路径长度检查
                        char game_folder_path[256] = {0};  // 增加缓冲区大小
                        int path_len = snprintf(game_folder_path, sizeof(game_folder_path), "%s/%s/%s", AUTOBACK_DIR_PATH, username, folder_name);
                        
                        // 检查路径长度是否超出限制
                        if (path_len >= sizeof(game_folder_path)) {
                            char log_buf[512] = {0};
                            snprintf(log_buf, sizeof(log_buf), "警告: 用户名 %s, 游戏 %s 的路径长度超出限制，无法创建文件夹", username, folder_name);
                            log_file_write(log_buf);
                            accountProfileClose(&profile);
                            continue;
                        }
                        
                        // 创建游戏名称文件夹
                        Result mkdir_rc = fsFsCreateDirectory(sdmc_fs, game_folder_path);
                        if (R_SUCCEEDED(mkdir_rc)) {
                            char log_buf[512] = {0};
                            snprintf(log_buf, sizeof(log_buf), "已成功创建游戏文件夹: %s", game_folder_path);
                            log_file_write(log_buf);
                        } else if (mkdir_rc == 0x402) { // FSERROR_PATH_ALREADY_EXISTS
                            // 文件夹已存在，不需要处理
                        } else {
                            char log_buf[512] = {0};
                            snprintf(log_buf, sizeof(log_buf), "警告: 无法创建游戏文件夹 %s: 0x%x", game_folder_path, mkdir_rc);
                            log_file_write(log_buf);
                        }
                    } else {
                        char log_buf[256] = {0};
                        snprintf(log_buf, sizeof(log_buf), "警告: 无法获取用户 %016lX 的配置文件数据: 0x%x", user_ids[i].uid[0], account_rc);
                        log_file_write(log_buf);
                    }
                    accountProfileClose(&profile);
                } else {
                    char log_buf[256] = {0};
                    snprintf(log_buf, sizeof(log_buf), "警告: 无法获取用户 %016lX 的配置文件: 0x%x", user_ids[i].uid[0], account_rc);
                    log_file_write(log_buf);
                }
            }
        }
    }
}

static void generate_save_archive(u64 tid) {
    if (tid == 0) return;
    
    // 添加调试日志：开始生成存档
    log_file_fwrite("准备为 TID: %016lX 生成存档", tid);
    
    // 标记是否成功生成本地存档
    bool local_backup_success = false;
    
    // 创建游戏文件夹
    create_game_folder(tid);
    
    // 只处理当前运行游戏的用户
    if (g_current_game_user_uid.uid[0] == 0 && g_current_game_user_uid.uid[1] == 0) {
        log_file_fwrite("警告: 未检测到当前运行游戏的用户，跳过为 TID: %016lX 生成存档", tid);
        return;
    }
    
    // 使用全局变量中的用户信息
    AccountUid target_user = g_current_game_user_uid;
    const char* username = g_current_game_user_name[0] ? g_current_game_user_name : "Unknown";
    
    // 添加调试日志：处理当前用户
    log_file_fwrite("已为用户 %s (%016lX%016lX) 生成存档", username, target_user.uid[0], target_user.uid[1]);
    
    FsFileSystem save_fs;
    FsSaveDataAttribute attr = {0};
    attr.application_id = tid;
    attr.uid = target_user;
    attr.save_data_type = FsSaveDataType_Account;
    
    // 使用fsOpenReadOnlySaveDataFileSystem挂载存档文件系统
    Result rc = fsOpenReadOnlySaveDataFileSystem(&save_fs, FsSaveDataSpaceId_User, &attr);
    if (R_SUCCEEDED(rc)) {
        // 添加调试日志：成功挂载存档文件系统
        log_file_fwrite("已成功挂载用户 %s 的存档文件系统", username);
        
        // 检查存档是否存在 - 尝试读取存档根目录
        FsDir dir;
        Result dir_rc = fsFsOpenDirectory(&save_fs, "/", FsDirOpenMode_ReadDirs | FsDirOpenMode_ReadFiles, &dir);
        
        if (R_SUCCEEDED(dir_rc)) {
            // 存档存在，继续生成ZIP文件
            s64 entry_count = 0;
            Result count_rc = fsDirGetEntryCount(&dir, &entry_count);
            fsDirClose(&dir);
            
            // 检查获取条目数量是否成功
            if (R_FAILED(count_rc)) {
                log_file_fwrite("警告: 无法获取用户 %s 的存档条目数量: 0x%x", username, count_rc);
                fsFsClose(&save_fs);
                return;
            }
            
            // 添加调试日志：存档条目数量
            log_file_fwrite("用户 %s 的存档条目数量: %ld", username, entry_count);
            
            if (entry_count > 0) {
                // 为当前用户创建存档ZIP文件
                struct mmz_Data mz = {0};
                
                // 调用mmz_build_zip生成存档元数据
                Result rc = mmz_build_zip(&mz, &save_fs, tid, target_user, FsSaveDataSpaceId_User);
                if (R_SUCCEEDED(rc)) {
                    // 添加调试日志：成功生成存档元数据
                    log_file_fwrite("已成功为用户 %s 生成存档元数据", username);
                    
                    // 确保元数据写入磁盘
                    Result flush_rc = fsFileFlush(&mz.fbuf_out);
                    if (R_FAILED(flush_rc)) {
                        log_file_fwrite("警告: 无法刷新用户 %s 的存档元数据文件: 0x%x", username, flush_rc);
                    }
                    
                    // 创建最终路径：/AutoBack/用户名/folder_name/游戏名_用户名_最近一次webdav重命名存档的时间戳_序列号.zip
                    char latest_timestamp[64] = {0};
                    int sequence_num = 1;
                    
                    // 获取最近一次WebDAV重命名存档的时间戳和序列号
                    get_latest_webdav_timestamp_and_sequence(username, folder_name, latest_timestamp, sizeof(latest_timestamp), &sequence_num);

                    char final_path[FS_MAX_PATH] = {0};
                    int path_len = snprintf(final_path, sizeof(final_path), "%s/%s/%s/%s_%s_%s_%d.zip", 
                             AUTOBACK_DIR_PATH, username, folder_name, folder_name, username, latest_timestamp, sequence_num);
                    
                    // 检查路径长度是否超出限制
                    if (path_len >= sizeof(final_path)) {
                        log_file_fwrite("警告: 最终路径长度 (%d 个字符) 超出限制，已截断", path_len);
                    }
                    
                    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
                    if (sdmc_fs != NULL) {
                        // 添加调试日志：获取SD卡文件系统成功
                        log_file_fwrite("已成功获取SD卡文件系统");
                        
                        // 确保用户目录存在
                        char user_dir[256] = {0};
                        snprintf(user_dir, sizeof(user_dir), "%s/%s", AUTOBACK_DIR_PATH, username);
                        Result user_dir_rc = fsFsCreateDirectory(sdmc_fs, user_dir);
                        if (R_FAILED(user_dir_rc) && user_dir_rc != 0x402) { // 0x402 = directory already exists
                            log_file_fwrite("警告: 无法创建用户目录 %s: 0x%x", user_dir, user_dir_rc);
                        }
                        
                        // 确保游戏文件夹存在
                        char game_dir[256] = {0};
                        snprintf(game_dir, sizeof(game_dir), "%s/%s/%s", AUTOBACK_DIR_PATH, username, folder_name);
                        Result game_dir_rc = fsFsCreateDirectory(sdmc_fs, game_dir);
                        if (R_FAILED(game_dir_rc) && game_dir_rc != 0x402) { // 0x402 = directory already exists
                            log_file_fwrite("警告: 无法创建游戏目录 %s: 0x%x", game_dir, game_dir_rc);
                        }
                        
                        // 管理存档数量：在创建新存档前检查并删除最旧的存档
                        manage_backup_count(username, folder_name);
                        
                        // 添加调试日志：开始流式传输ZIP到SD卡
                        log_file_fwrite("已开始流式传输用户 %s 的存档元数据到SD卡", username);
                        
                        // 流式传输ZIP到SD卡
                        rc = stream_zip_to_sdcard(&mz, sdmc_fs, final_path);
                        
                        // 关闭临时文件句柄
                        fsFileClose(&mz.fbuf_out);
                        
                        // 传输完成后清理临时文件
                        char temp_path[FS_MAX_PATH] = {0};
                        mzz_build_temp_path(temp_path, tid, target_user, FsSaveDataSpaceId_User);
                        if (sdmc_fs != NULL) {
                            Result delete_rc = fsFsDeleteFile(sdmc_fs, temp_path);
                            if (R_FAILED(delete_rc) && delete_rc != 0x202) { // 0x202 = file not found
                                log_file_fwrite("警告: 无法删除临时文件 %s: 0x%x", temp_path, delete_rc);
                            }
                        }

                        // 使用get_app_log_name获取游戏名
                        NcmContentId content_id = {0};
                        struct AppName app_name = {0};
                        get_app_log_name(tid, &content_id, &app_name);

                        if (R_SUCCEEDED(rc)) {
                            log_file_fwrite("已成功创建用户 %s 的存档元数据: %s", username, final_path);
                            // 标记本地存档生成成功
                            local_backup_success = true;
                            // 备份完成时发送Ultrahand通知
                            create_ultrahand_notification("本地备份完成", 1);
                            // 写入备份记录: "保存成功|游戏名|用户名|时间戳"
                            if (!webdav_config.enabled) backuplog_fwrite("本地备份成功|%s|%s|%s", app_name.str, username, latest_timestamp);
                        } else {
                            log_file_fwrite("警告: 无法流式传输用户 %s 的存档元数据到SD卡: 0x%x", username, rc);
                            // 备份失败时发送Ultrahand通知
                            create_ultrahand_notification("本地备份失败", 2);
                            // 写入备份记录: "保存失败|游戏名|用户名|时间戳"
                            backuplog_fwrite("本地备份失败|%s|%s|%s", app_name.str, username, latest_timestamp);
                        }
                    } else {
                        log_file_write("警告: 无法获取SD卡文件系统");
                        create_ultrahand_notification("SD卡文件系统不可用", 2);
                    }
                    
                    // 注意：不在这里删除临时文件，因为mmz_read还需要读取它
                    // 清理工作将在stream_zip_to_sdcard完成后进行
                } else {
                    log_file_fwrite("警告: 无法为TID %016lX 和用户 %s 生成存档元数据: 0x%x", tid, username, rc);
                    create_ultrahand_notification("本地备份生成失败", 2);
                    
                    // 注意：不在这里删除临时文件，因为mmz_read还需要读取它
                    // 清理工作将在stream_zip_to_sdcard完成后进行
                }
            } else {
                // 存档目录存在但为空，跳过
                log_file_fwrite("警告: 存档目录为空，跳过TID %016lX 和用户 %s 的存档元数据生成", tid, username);
            }
        } else if (dir_rc == 0x7D402) { // FSERROR_PATH_NOT_FOUND
            log_file_fwrite("警告: 未找到TID %016lX 和用户 %s 的存档元数据，跳过", tid, username);
        } else {
            // 其他错误，记录日志但继续
            log_file_fwrite("警告: 检查TID %016lX 和用户 %s 的存档元数据时出错: 0x%x", tid, username, dir_rc);
        }
        
        // 关闭存档文件系统
        fsFsClose(&save_fs);
    } else {
        char log_buf[512] = {0};
        snprintf(log_buf, sizeof(log_buf), "警告: 无法打开TID %016lX 和用户 %s 的存档文件系统: 0x%x", tid, username, rc);
        log_file_write(log_buf);
    }
    
    // 添加调试日志：完成生成存档
    log_file_fwrite("已完成为TID %016lX 和用户 %s 生成存档元数据", tid, username);
    
    // 本地存档生成完成后，检测网络连接状态和webdav配置
    if (local_backup_success) {
        Result nifm_rc = nifmInitialize(NifmServiceType_User);
        if (R_SUCCEEDED(nifm_rc)) {
            u32 ip_addr;
            Result ip_rc = nifmGetCurrentIpAddress(&ip_addr);
            
            if (R_SUCCEEDED(ip_rc)) {
                // 联网状态，检查webdav是否启用
                if (webdav_config.enabled) {
                    // 联网且webdav启用，执行握手操作
                    struct in_addr addr;
                    addr.s_addr = ip_addr;
                    log_file_fwrite("已连接网络 (IP: %s) 且 WebDAV 已启用，正在执行握手", inet_ntoa(addr));
                    
                    // 执行WebDAV握手
                    bool handshake_success = webdav_handshake();
                    if (handshake_success) {
                        log_file_fwrite("已成功完成 WebDAV 握手并上传存档元数据");
                    } else {
                        log_file_fwrite("WebDAV 握手失败，但本地备份已成功完成");
                    }
                } else {
                    // 联网但webdav未启用
                    struct in_addr addr;
                    addr.s_addr = ip_addr;
                    log_file_fwrite("已连接网络 (IP: %s) 但 WebDAV 未启用，本地备份已完成", inet_ntoa(addr));
                }
            } else {
                // 未联网状态
                log_file_fwrite("未连接网络，本地备份已完成");
            }
            
            nifmExit();
        } else {
            // nifm初始化失败，假设未联网
            log_file_write("已初始化网络服务失败，假设为离线模式，本地备份已完成");
        }
    } else {
        log_file_write("本地备份失败，跳过 WebDAV 握手");
    }
}

// 存档文件管理
static time_t parse_timestamp_from_filename(const char* filename, int* sequence) {
    struct tm tm_info = {0};
    time_t timestamp = 0;
    
    log_file_fwrite("[PARSE_TIMESTAMP] 正在解析文件名: %s", filename);
    
    // 初始化序列号
    if (sequence) *sequence = 0;
    
    // 创建文件名副本并进行URL解码（处理WebDAV中的URL编码）
    char decoded_filename[512];
    strncpy(decoded_filename, filename, sizeof(decoded_filename) - 1);
    decoded_filename[sizeof(decoded_filename) - 1] = '\0';
    url_decode(decoded_filename);
    
    log_file_fwrite("[PARSE_TIMESTAMP] 解码后的文件名: %s", decoded_filename);
    
    // 查找最后一个下划线（可能是时间戳或序列号分隔符）
    char* last_underscore = strrchr(decoded_filename, '_');
    if (last_underscore == NULL) {
        log_file_fwrite("[PARSE_TIMESTAMP] 错误: 文件名中未找到下划线分隔符");
        return 0;
    }
    
    char* zip_ext = strstr(last_underscore, ".zip");
    if (zip_ext == NULL) {
        log_file_fwrite("[PARSE_TIMESTAMP] 错误: 文件名中未找到 .zip 扩展名");
        return 0;
    }
    
    // 检查是否是序列号格式（时间戳_序列号.zip）
    char seq_str[16] = {0};
    size_t seq_len = zip_ext - (last_underscore + 1);
    bool has_sequence = false;
    
    if (seq_len > 0 && seq_len < sizeof(seq_str)) {
        strncpy(seq_str, last_underscore + 1, seq_len);
        seq_str[seq_len] = '\0';
        
        // 检查是否为纯数字（序列号）
        bool is_sequence = true;
        for (size_t i = 0; i < seq_len; i++) {
            if (!isdigit((unsigned char)seq_str[i])) {
                is_sequence = false;
                break;
            }
        }
        
        if (is_sequence) {
            has_sequence = true;
            if (sequence) *sequence = atoi(seq_str);
            log_file_fwrite("[PARSE_TIMESTAMP] 检测到序列号格式，序列号: %d", *sequence);
        }
    }
    
    if (has_sequence) {
        // 带序列号格式：查找时间戳部分的开始（倒数第二个下划线）
        char* time_underscore = last_underscore - 1;
        while (time_underscore > decoded_filename && *time_underscore != '_') {
            time_underscore--;
        }
        if (time_underscore == decoded_filename || *time_underscore != '_') {
            log_file_fwrite("[PARSE_TIMESTAMP] 错误: 序列号格式中未找到时间戳分隔符");
            return 0;
        }
        
        // 解析时间戳部分
        char* time_start = time_underscore + 1;
        size_t time_len = last_underscore - time_start;
        
        if (time_len > 0 && time_len < 64) {
            char time_str[64] = {0};
            strncpy(time_str, time_start, time_len);
            time_str[time_len] = '\0';
            log_file_fwrite("[PARSE_TIMESTAMP] 序列号格式，提取的时间字符串: %s", time_str);
            
            // 转换时间格式并解析
            char* at_pos = strchr(time_str, '@');
            if (at_pos != NULL) {
                *at_pos = ' ';
                char* dot_pos;
                while ((dot_pos = strchr(time_str, '.')) != NULL) {
                    *dot_pos = ':';
                }
                
                log_file_fwrite("[PARSE_TIMESTAMP] 序列号格式，转换后的时间格式: %s", time_str);
                if (custom_strptime(time_str, "%Y %m %d %H:%M:%S", &tm_info)) {
                    timestamp = mktime(&tm_info);
                    log_file_fwrite("[PARSE_TIMESTAMP] 序列号格式，成功解析时间戳: timestamp=%ld", timestamp);
                } else {
                    log_file_fwrite("[PARSE_TIMESTAMP] 错误: 序列号格式使用 custom_strptime 解析时间戳失败");
                }
            } else {
                log_file_fwrite("[PARSE_TIMESTAMP] 错误: 序列号格式中未找到 @ 分隔符");
            }
        } else {
            log_file_fwrite("[PARSE_TIMESTAMP] 错误: 序列号格式中时间字符串长度无效");
        }
    } else {
        // 单时间戳格式
        log_file_fwrite("[PARSE_TIMESTAMP] 检测到单时间戳格式");
        char* time_start = last_underscore + 1;
        size_t time_len = zip_ext - time_start;
        
        if (time_len > 0 && time_len < 64) {
            char time_str[64] = {0};
            strncpy(time_str, time_start, time_len);
            time_str[time_len] = '\0';
            log_file_fwrite("[PARSE_TIMESTAMP] 单时间戳格式，提取的时间字符串: %s", time_str);
            
            // 解析时间戳格式：YYYY.MM.DD@HH.MM.SS
            char* at_pos = strchr(time_str, '@');
            if (at_pos != NULL) {
                *at_pos = ' ';
                char* dot_pos;
                while ((dot_pos = strchr(time_str, '.')) != NULL) {
                    *dot_pos = ':';
                }
                
                log_file_fwrite("[PARSE_TIMESTAMP] Converted time format: %s", time_str);
                if (custom_strptime(time_str, "%Y %m %d %H:%M:%S", &tm_info)) {
                    timestamp = mktime(&tm_info);
                    log_file_fwrite("[PARSE_TIMESTAMP] Single timestamp format parsed successfully: timestamp=%ld", timestamp);
                } else {
                    log_file_fwrite("[PARSE_TIMESTAMP] Error: Failed to parse single timestamp format with custom_strptime");
                }
            } else {
                log_file_fwrite("[PARSE_TIMESTAMP] Error: @ separator not found in single timestamp format time string");
            }
        } else {
            log_file_fwrite("[PARSE_TIMESTAMP] Error: Invalid length for single timestamp format time string");
        }
    }
    
    log_file_fwrite("[PARSE_TIMESTAMP] Parsing completed, final timestamp: %ld, sequence: %d", timestamp, sequence ? *sequence : 0);
    return timestamp;
}

static int compare_save_files(const void* a, const void* b) {
    const struct SaveFileInfo* file_a = (const struct SaveFileInfo*)a;
    const struct SaveFileInfo* file_b = (const struct SaveFileInfo*)b;
    
    // 首先按时间戳排序（从新到旧）
    if (file_a->timestamp != file_b->timestamp) {
        return (file_a->timestamp > file_b->timestamp) ? -1 : 1;
    }
    
    // 时间戳相同，按序列号排序（从大到小）
    if (file_a->sequence != file_b->sequence) {
        return (file_a->sequence > file_b->sequence) ? -1 : 1;
    }
    
    // 时间戳和序列号都相同，按文件名排序
    return strcmp(file_a->filename, file_b->filename);
}

static void manage_backup_count(const char* username, const char* game_folder) {
    // 参数验证
    if (username == NULL || username[0] == '\0') {
        char debug_buf[128];
        snprintf(debug_buf, sizeof(debug_buf), "manage_backup_count: 无效的用户名参数");
        log_file_write(debug_buf);
        return;
    }
    
    if (game_folder == NULL || game_folder[0] == '\0') {
        char debug_buf[128];
        snprintf(debug_buf, sizeof(debug_buf), "manage_backup_count: 无效的游戏文件夹参数");
        log_file_write(debug_buf);
        return;
    }
    
    if (g_maxback <= 0) {
        return; // maxback未启用或设置为0
    }
    
    // 清理用户名
    char sanitized_username[64];
    strncpy(sanitized_username, username, sizeof(sanitized_username) - 1);
    sanitized_username[sizeof(sanitized_username) - 1] = '\0';
    sanitize_filename(sanitized_username);
    
    // 验证清理后的用户名是否有效
    bool has_valid_chars = false;
    for (int i = 0; sanitized_username[i] != '\0'; i++) {
        if (isalnum((unsigned char)sanitized_username[i]) || sanitized_username[i] == '_' || sanitized_username[i] == '-') {
            has_valid_chars = true;
            break;
        }
    }
    
    if (!has_valid_chars || sanitized_username[0] == '\0') {
        char debug_buf[128];
        snprintf(debug_buf, sizeof(debug_buf), "manage_backup_count: 清理后的用户名无效: %s", username);
        log_file_write(debug_buf);
        return;
    }
    
    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
    if (sdmc_fs == NULL) {
        char debug_buf[128];
        snprintf(debug_buf, sizeof(debug_buf), "manage_backup_count: 无法获取SD卡文件系统");
        log_file_write(debug_buf);
        return;
    }
    
    char search_pattern[FS_MAX_PATH];
    snprintf(search_pattern, sizeof(search_pattern), "%s/%s/%s", AUTOBACK_DIR_PATH, sanitized_username, game_folder);
    
    // 打开目录
    FsDir search_dir;
    Result dir_rc = fsFsOpenDirectory(sdmc_fs, search_pattern, FsDirOpenMode_ReadFiles, &search_dir);
    if (R_FAILED(dir_rc)) {
        return;
    }
    
    // 收集所有ZIP文件
    struct SaveFileInfo* save_files = NULL;
    int file_count = 0;
    int max_files = 0;
    
    s64 total_entries;
    FsDirectoryEntry entry;
    while (R_SUCCEEDED(fsDirRead(&search_dir, &total_entries, 1, &entry)) && total_entries == 1) {
        if (entry.type == FsDirEntryType_File && strstr(entry.name, ".zip")) {
            // 动态扩展数组
            if (file_count >= max_files) {
                max_files = max_files == 0 ? 16 : max_files * 2;
                struct SaveFileInfo* new_files = realloc(save_files, max_files * sizeof(struct SaveFileInfo));
                if (new_files == NULL) {
                    break;
                }
                save_files = new_files;
            }
            
            // 填充文件信息
            struct SaveFileInfo* file_info = &save_files[file_count];
            memset(file_info, 0, sizeof(struct SaveFileInfo));
            
            // 构造完整路径
            snprintf(file_info->path, sizeof(file_info->path), "%s/%s", search_pattern, entry.name);
            strncpy(file_info->filename, entry.name, sizeof(file_info->filename) - 1);
            file_info->filename[sizeof(file_info->filename) - 1] = '\0';
            
            // 解析时间戳和序列号
            int sequence = 0;
            time_t timestamp = parse_timestamp_from_filename(entry.name, &sequence);
            file_info->timestamp = timestamp;
            file_info->sequence = sequence;
            
            file_count++;
        }
    }
    
    fsDirClose(&search_dir);
    
    if (file_count == 0) {
        if (save_files) {
            free(save_files);
        }
        return;
    }
    
    // 按时间戳和序列号排序（从新到旧）
    qsort(save_files, file_count, sizeof(struct SaveFileInfo), compare_save_files);
    
    // 输出排序结果用于调试
    for (int i = 0; i < file_count && i < 5; i++) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "[BACKUP_MANAGE] Sorted[%d]: %s (timestamp=%ld, sequence=%d)", 
                i, save_files[i].filename, save_files[i].timestamp, save_files[i].sequence);
        log_file_write(debug_buf);
    }
    
    // 检查是否需要删除存档
    if (file_count >= g_maxback) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "发现 %d 个存档文件，maxback=%d，删除最旧的 %d 个文件", 
                 file_count, g_maxback, file_count - g_maxback + 1);
        log_file_write(debug_buf);
        
        // 删除最旧的存档，保留maxback-1个（由于排序是从新到旧，最旧的在数组末尾）
        for (int i = file_count - 1; i >= g_maxback - 1; i--) {
            Result delete_rc = fsFsDeleteFile(sdmc_fs, save_files[i].path);
            if (R_SUCCEEDED(delete_rc)) {
                snprintf(debug_buf, sizeof(debug_buf), "已删除旧存档文件: %s", save_files[i].filename);
                log_file_write(debug_buf);
            } else {
                snprintf(debug_buf, sizeof(debug_buf), "删除存档文件 %s 失败: 0x%x", save_files[i].filename, delete_rc);
                log_file_write(debug_buf);
            }
        }
    }
    
    if (save_files) {
        free(save_files);
    }
}

// 管理WebDAV端存档数量，删除最旧的远程存档
static void manage_webdav_backup_count(const char* username, const char* game_folder) {
    if (g_maxback <= 0) {
        return; // maxback未启用或设置为0
    }
    
    // 参数验证
    if (!username || strlen(username) == 0) {
        char debug_buf[256] = {0};
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理失败: 用户名为空");
        log_file_write(debug_buf);
        return;
    }
    
    if (!game_folder || strlen(game_folder) == 0) {
        char debug_buf[256] = {0};
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理失败: 游戏文件夹为空");
        log_file_write(debug_buf);
        return;
    }
    
    CURL* curl;
    CURLcode res;
    char url[512];
    char debug_buf[256];
    
    // 清理和验证用户名
    char sanitized_username[256] = {0};
    strncpy(sanitized_username, username, sizeof(sanitized_username) - 1);
    sanitize_filename(sanitized_username);
    
    // 验证清理后的用户名是否有效
    bool has_valid_chars = false;
    for (int i = 0; sanitized_username[i] != '\0'; i++) {
        if (isalnum((unsigned char)sanitized_username[i]) || sanitized_username[i] == '_' || sanitized_username[i] == '-') {
            has_valid_chars = true;
            break;
        }
    }
    
    if (!has_valid_chars || strlen(sanitized_username) == 0) {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理失败: 清理后的用户名无效: %s", username);
        log_file_write(debug_buf);
        return;
    }
    
    // 对游戏文件夹名进行URL编码，处理空格等特殊字符
    char encoded_game_folder[256];
    strncpy(encoded_game_folder, game_folder, sizeof(encoded_game_folder) - 1);
    encoded_game_folder[sizeof(encoded_game_folder) - 1] = '\0';
    
    // 简单的空格替换为%20（更完整的URL编码需要更复杂的处理）
    char* space = encoded_game_folder;
    while ((space = strchr(space, ' ')) != NULL) {
        *space = '%';
        memmove(space + 3, space + 1, strlen(space));
        space[1] = '2';
        space[2] = '0';
        space += 3;
    }
    
    // 构造WebDAV目录URL - 修改为与本地路径一致的结构
    if (webdav_config.basepath[0] != '\0') {
        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/' && webdav_config.basepath[0] == '/') {
            snprintf(url, sizeof(url), "%s%sAutoBack/%s/%s/", 
                     webdav_config.origin, webdav_config.basepath + 1, sanitized_username, encoded_game_folder);
        } else if (webdav_config.origin[strlen(webdav_config.origin)-1] != '/' && webdav_config.basepath[0] != '/') {
            snprintf(url, sizeof(url), "%s/%s/AutoBack/%s/%s/", 
                     webdav_config.origin, webdav_config.basepath, sanitized_username, encoded_game_folder);
        } else {
            snprintf(url, sizeof(url), "%s%sAutoBack/%s/%s/", 
                     webdav_config.origin, webdav_config.basepath, sanitized_username, encoded_game_folder);
        }
    } else {
        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/') {
            snprintf(url, sizeof(url), "%sAutoBack/%s/%s/", webdav_config.origin, sanitized_username, encoded_game_folder);
        } else {
            snprintf(url, sizeof(url), "%s/AutoBack/%s/%s/", webdav_config.origin, sanitized_username, encoded_game_folder);
        }
    }
    
    snprintf(debug_buf, sizeof(debug_buf), "正在管理 WebDAV 存档数量，用户: %s, 游戏: %s", sanitized_username, game_folder);
    log_file_write(debug_buf);
    
    snprintf(debug_buf, sizeof(debug_buf), "PROPFIND URL: %s", url);
    log_file_write(debug_buf);
    
    curl = curl_easy_init();
    if (!curl) {
        snprintf(debug_buf, sizeof(debug_buf), "初始化 CURL 失败，用于 WebDAV 存档管理");
        log_file_write(debug_buf);
        return;
    }
    
    // 设置CURL选项进行PROPFIND请求
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, "PROPFIND");
    curl_easy_setopt(curl, CURLOPT_USERAGENT, "libnx-webdav-backup-mgmt/1.0");
    curl_easy_setopt(curl, CURLOPT_HTTPAUTH, (long)CURLAUTH_BASIC);
    curl_easy_setopt(curl, CURLOPT_USERNAME, webdav_config.username);
    curl_easy_setopt(curl, CURLOPT_PASSWORD, webdav_config.password);
    
    struct curl_slist *headers = NULL;
    headers = curl_slist_append(headers, "Depth: 1");
    headers = curl_slist_append(headers, "Content-Type: text/xml; charset=\"utf-8\"");
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
    
    // 添加PROPFIND XML请求体
    const char* propfind_xml = "<?xml version=\"1.0\" encoding=\"utf-8\" ?>"
                                "<D:propfind xmlns:D=\"DAV:\">"
                                "<D:prop>"
                                "<D:displayname/>"
                                "</D:prop>"
                                "</D:propfind>";
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, propfind_xml);
    
    // 设置回调函数来接收响应数据
    struct WebDAVResponseData response_data = {0};
    
    // 初始化响应数据缓冲区
    response_data.data = malloc(1);
    if (response_data.data == NULL) {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理失败: 分配响应数据内存失败");
        log_file_write(debug_buf);
        curl_easy_cleanup(curl);
        curl_slist_free_all(headers);
        return;
    }
    response_data.data[0] = '\0';
    response_data.size = 0;
    
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, webdav_response_write_callback);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, &response_data);
    
    // 执行PROPFIND请求
    res = curl_easy_perform(curl);
    
    if (res == CURLE_OK) {
        long http_code = 0;
        curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &http_code);
        
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理成功: HTTP %ld", http_code);
        log_file_write(debug_buf);
        
        if (http_code == 207) { // Multi-Status，PROPFIND成功
          
            // 添加调试日志，输出原始XML响应
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理成功: 原始XML响应 (前1000字符): %.1000s", response_data.data ? response_data.data : "(null)");
            log_file_write(debug_buf);
            // 输出XML响应总长度
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理成功: XML响应总长度: %zu 字节", response_data.size);
            log_file_write(debug_buf);
            
            // 查找所有包含用户名的ZIP文件
            char* file_list[128]; // 最多支持128个文件
            int file_count = 0;
            char* current_pos = response_data.data;
            
            // 添加调试信息：检查XML响应是否包含预期的命名空间
            if (strstr(response_data.data, "xmlns:d=\"DAV:\"") == NULL && 
                strstr(response_data.data, "xmlns:D=\"DAV:\"") == NULL) {
                snprintf(debug_buf, sizeof(debug_buf), "WebDAV 存档管理成功: XML响应不包含预期的 DAV 命名空间");
                log_file_write(debug_buf);
            }
            
            // 检查XML响应是否包含multistatus标签
            if (strstr(response_data.data, "multistatus") == NULL) {
                snprintf(debug_buf, sizeof(debug_buf), "Warning: XML response does not contain multistatus tag");
                log_file_write(debug_buf);
            }
            
            while (current_pos != NULL && file_count < 128) {
                // 查找href标签，支持多种命名空间格式
                char* href_start = strstr(current_pos, "<d:href>");
                if (href_start == NULL) {
                    href_start = strstr(current_pos, "<D:href>");
                    if (href_start == NULL) {
                        href_start = strstr(current_pos, "<href>");
                        if (href_start == NULL) {
                            // 添加调试信息：记录找不到href标签时的位置
                            snprintf(debug_buf, sizeof(debug_buf), "No href tag found at position: %ld", current_pos - response_data.data);
                            log_file_write(debug_buf);
                            break;
                        } else {
                            href_start += 6; // 跳过<href>
                        }
                    } else {
                        href_start += 8; // 跳过<D:href>
                    }
                } else {
                    href_start += 8; // 跳过<d:href>
                }
                
                // 查找对应的结束标签
                char* href_end = strstr(href_start, "</d:href>");
                if (href_end == NULL) {
                    href_end = strstr(href_start, "</D:href>");
                    if (href_end == NULL) {
                        href_end = strstr(href_start, "</href>");
                        if (href_end == NULL) break;
                    }
                }
                
                // 提取文件名
                size_t href_len = href_end - href_start;
                char filename[256];
                if (href_len < sizeof(filename)) {
                    strncpy(filename, href_start, href_len);
                    filename[href_len] = '\0';
                    
                    // 添加调试信息：记录找到的文件名
                    snprintf(debug_buf, sizeof(debug_buf), "Found file in XML: %s", filename);
                    log_file_write(debug_buf);
                    
                    // 检查是否是ZIP文件（移除用户名匹配逻辑）
                    if (strstr(filename, ".zip")) {
                        snprintf(debug_buf, sizeof(debug_buf), "File is a .zip file: %s", filename);
                        log_file_write(debug_buf);
                        // 提取纯文件名（不含路径）
                        char* last_slash = strrchr(filename, '/');
                        if (last_slash != NULL) {
                            last_slash++;
                        } else {
                            last_slash = filename;
                        }
                        
                        // 分配内存并存储文件名
                        size_t name_len = strlen(last_slash) + 1;
                        file_list[file_count] = malloc(name_len);
                        if (file_list[file_count] != NULL) {
                            strncpy(file_list[file_count], last_slash, name_len);
                            file_count++;
                        }
                    }
                }
                
                // 根据结束标签长度更新current_pos
                if (strstr(href_start, "</d:href>") == href_end) {
                    current_pos = href_end + 9; // 跳过</d:href>
                } else if (strstr(href_start, "</D:href>") == href_end) {
                    current_pos = href_end + 9; // 跳过</D:href>
                } else {
                    current_pos = href_end + 7; // 跳过</href>
                }
            }
            
            snprintf(debug_buf, sizeof(debug_buf), "Found %d WebDAV backup files", file_count);
            log_file_write(debug_buf);
            
            // 如果文件数量超过maxback，删除最旧的文件
            if (file_count >= g_maxback) {
                // 按时间戳排序文件（从旧到新，这样最旧的文件在数组前面）
                for (int i = 0; i < file_count - 1; i++) {
                    for (int j = i + 1; j < file_count; j++) {
                        // 解析两个文件的时间戳进行比较
                        int sequence_i = 0, sequence_j = 0;
                        time_t timestamp_i = parse_timestamp_from_filename(file_list[i], &sequence_i);
                        time_t timestamp_j = parse_timestamp_from_filename(file_list[j], &sequence_j);
                        
                        // 如果时间戳解析失败，使用文件名排序作为后备
                        if (timestamp_i == 0 && timestamp_j == 0) {
                            if (strcmp(file_list[i], file_list[j]) > 0) {
                                char* temp = file_list[i];
                                file_list[i] = file_list[j];
                                file_list[j] = temp;
                            }
                        } else if (timestamp_i == 0) {
                            // 文件i没有有效时间戳，排在后面
                            char* temp = file_list[i];
                            file_list[i] = file_list[j];
                            file_list[j] = temp;
                        } else if (timestamp_j == 0) {
                            // 文件j没有有效时间戳，排在后面
                            // 不交换，文件i已经排在前面
                        } else {
                            // 两个文件都有有效时间戳，按时间戳排序（从新到旧）
                            if (timestamp_i < timestamp_j) {
                                char* temp = file_list[i];
                                file_list[i] = file_list[j];
                                file_list[j] = temp;
                            }
                        }
                    }
                }
                
                // 删除最旧的文件（排序后的后面的文件，因为排序是从新到旧）
                int files_to_delete = file_count - g_maxback + 1;
                for (int i = file_count - 1; i >= file_count - files_to_delete && i >= 0; i--) {
                    // 构造删除URL - 使用autoback/{用户名}/{游戏名}格式
                    char delete_url[512];
                    if (webdav_config.basepath[0] != '\0') {
                        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/' && webdav_config.basepath[0] == '/') {
                            snprintf(delete_url, sizeof(delete_url), "%s%sAutoBack/%s/%s/%s", 
                                     webdav_config.origin, webdav_config.basepath + 1, sanitized_username, encoded_game_folder, file_list[i]);
                        } else if (webdav_config.origin[strlen(webdav_config.origin)-1] != '/' && webdav_config.basepath[0] != '/') {
                            snprintf(delete_url, sizeof(delete_url), "%s/%s/AutoBack/%s/%s/%s", 
                                     webdav_config.origin, webdav_config.basepath, sanitized_username, encoded_game_folder, file_list[i]);
                        } else {
                            snprintf(delete_url, sizeof(delete_url), "%s%sAutoBack/%s/%s/%s", 
                                     webdav_config.origin, webdav_config.basepath, sanitized_username, encoded_game_folder, file_list[i]);
                        }
                    } else {
                        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/') {
                            snprintf(delete_url, sizeof(delete_url), "%sAutoBack/%s/%s/%s", webdav_config.origin, sanitized_username, encoded_game_folder, file_list[i]);
                        } else {
                            snprintf(delete_url, sizeof(delete_url), "%s/AutoBack/%s/%s/%s", webdav_config.origin, sanitized_username, encoded_game_folder, file_list[i]);
                        }
                    }
                    
                    // 执行DELETE请求
                    CURL* delete_curl = curl_easy_init();
                    if (delete_curl) {
                        curl_easy_setopt(delete_curl, CURLOPT_URL, delete_url);
                        curl_easy_setopt(delete_curl, CURLOPT_CUSTOMREQUEST, "DELETE");
                        curl_easy_setopt(delete_curl, CURLOPT_USERAGENT, "libnx-webdav-backup-mgmt/1.0");
                        curl_easy_setopt(delete_curl, CURLOPT_HTTPAUTH, (long)CURLAUTH_BASIC);
                        curl_easy_setopt(delete_curl, CURLOPT_USERNAME, webdav_config.username);
                        curl_easy_setopt(delete_curl, CURLOPT_PASSWORD, webdav_config.password);
                        
                        CURLcode delete_res = curl_easy_perform(delete_curl);
                        if (delete_res == CURLE_OK) {
                            long delete_http_code = 0;
                            curl_easy_getinfo(delete_curl, CURLINFO_RESPONSE_CODE, &delete_http_code);
                            
                            if (delete_http_code == 204 || delete_http_code == 200) {
                                snprintf(debug_buf, sizeof(debug_buf), "Deleted old WebDAV backup: %s", file_list[i]);
                                log_file_write(debug_buf);
                            } else {
                                snprintf(debug_buf, sizeof(debug_buf), "Failed to delete WebDAV backup %s: HTTP %ld", file_list[i], delete_http_code);
                                log_file_write(debug_buf);
                            }
                        } else {
                            snprintf(debug_buf, sizeof(debug_buf), "DELETE request failed for %s: %d", file_list[i], delete_res);
                            log_file_write(debug_buf);
                        }
                        
                        curl_easy_cleanup(delete_curl);
                    }
                }
            }
            
            // 释放内存
            for (int i = 0; i < file_count; i++) {
                if (file_list[i] != NULL) {
                    free(file_list[i]);
                }
            }
        } else {
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV PROPFIND failed for backup management: HTTP %ld", http_code);
            log_file_write(debug_buf);
        }
    } else {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV PROPFIND request failed: %d", res);
        log_file_write(debug_buf);
    }
    
    // 清理资源
    curl_easy_cleanup(curl);
    curl_slist_free_all(headers);
    if (response_data.data != NULL) {
        free(response_data.data);
    }
}

// 文件流处理
static Result stream_zip_to_sdcard(struct mmz_Data* mz, FsFileSystem* sdmc_fs, const char* output_path) {
    Result rc;
    FsFile output_file;
    
    // 参数验证
    if (!mz || !sdmc_fs || !output_path) {
        return -1;
    }
    
    // Add debug log：开始流式传输
    char debug_buf[256] = {0};
    snprintf(debug_buf, sizeof(debug_buf), "Starting streaming to %s", output_path);
    log_file_write(debug_buf);
    
    // 创建输出文件
    rc = fsFsCreateFile(sdmc_fs, output_path, 0, 0);
    if (R_FAILED(rc) && rc != 0x2EE202) { // 忽略已存在的错误
        snprintf(debug_buf, sizeof(debug_buf), "Failed to create file %s: 0x%x", output_path, rc);
        log_file_write(debug_buf);
        return rc;
    } else if (rc == 0x2EE202) {
        snprintf(debug_buf, sizeof(debug_buf), "File %s already exists, will overwrite", output_path);
        log_file_write(debug_buf);
    } else {
        snprintf(debug_buf, sizeof(debug_buf), "Successfully created file %s", output_path);
        log_file_write(debug_buf);
    }
    
    // 打开文件
    rc = fsFsOpenFile(sdmc_fs, output_path, FsOpenMode_Read|FsOpenMode_Write|FsOpenMode_Append, &output_file);
    if (R_FAILED(rc)) {
        snprintf(debug_buf, sizeof(debug_buf), "Failed to open file %s: 0x%x", output_path, rc);
        log_file_write(debug_buf);
        return rc;
    }
    
    snprintf(debug_buf, sizeof(debug_buf), "Successfully opened file %s for writing", output_path);
    log_file_write(debug_buf);
    
    // 流式传输ZIP数据
    u64 total_written = 0;
    u8 buffer[8192] = {0}; // 8KB缓冲区，初始化为0
    int consecutive_errors = 0;
    const int MAX_CONSECUTIVE_ERRORS = 3;
    
    while (1) {
        // 清空缓冲区
        memset(buffer, 0, sizeof(buffer));
        
        int bytes_read = mmz_read(mz, buffer, sizeof(buffer));
        if (bytes_read < 0) {
            // 错误处理
            consecutive_errors++;
            snprintf(debug_buf, sizeof(debug_buf), "Error reading ZIP data: %d (consecutive errors: %d)", bytes_read, consecutive_errors);
            log_file_write(debug_buf);
            
            if (consecutive_errors >= MAX_CONSECUTIVE_ERRORS) {
                snprintf(debug_buf, sizeof(debug_buf), "Too many consecutive read errors, aborting");
                log_file_write(debug_buf);
                fsFileClose(&output_file);
                return -1;
            }
            
            // 短暂延迟后重试
            svcSleepThread(1000000); // 1ms
            continue;
        }
        
        // 重置错误计数器
        consecutive_errors = 0;
        
        if (bytes_read == 0) {
            // 传输完成
            snprintf(debug_buf, sizeof(debug_buf), "Finished reading ZIP data, total bytes: %lu", total_written);
            log_file_write(debug_buf);
            break;
        }
        
        // 验证读取的字节数是否合理
        if (bytes_read > sizeof(buffer)) {
            snprintf(debug_buf, sizeof(debug_buf), "Invalid bytes_read value: %d (buffer size: %zu)", bytes_read, sizeof(buffer));
            log_file_write(debug_buf);
            fsFileClose(&output_file);
            return -1;
        }
        
        // 写入SD卡 - 修复偏移量和bytes_written的使用
        rc = fsFileWrite(&output_file, total_written, buffer, bytes_read, FsWriteOption_None);
        if (R_FAILED(rc)) {
            snprintf(debug_buf, sizeof(debug_buf), "Failed to write to file %s: 0x%x (tried to write %d bytes at offset %lu)", output_path, rc, bytes_read, total_written);
            log_file_write(debug_buf);
            fsFileClose(&output_file);
            return rc;
        }
        
        total_written += bytes_read;
        
        // 定期刷新以防止缓冲区溢出
        if (total_written % (1024 * 1024) == 0) { // 每1MB刷新一次
            rc = fsFileFlush(&output_file);
            if (R_FAILED(rc)) {
                snprintf(debug_buf, sizeof(debug_buf), "Failed to flush file during write: 0x%x", rc);
                log_file_write(debug_buf);
                fsFileClose(&output_file);
                return rc;
            }
        }
    }
    
    // 刷新文件缓冲区确保数据写入
    rc = fsFileFlush(&output_file);
    if (R_FAILED(rc)) {
        snprintf(debug_buf, sizeof(debug_buf), "Failed to flush file %s: 0x%x, total bytes written: %lu", output_path, rc, total_written);
        log_file_write(debug_buf);
        fsFileClose(&output_file);
        return rc;
    } else {
        // 添加调试日志：完成文件写入
        snprintf(debug_buf, sizeof(debug_buf), "Successfully flushed file %s, total bytes written: %lu", output_path, total_written);
        log_file_write(debug_buf);
    }
    
    // 关闭文件
    fsFileClose(&output_file);
    return 0;
}

// ========== WebDAV云存储服务 ==========

// WebDAV连接与认证
static bool webdav_handshake(void) {
    CURL *curl;
    CURLcode res;
    char url[128];
    bool handshake_success = false;
    
    // 添加调试日志
    char debug_buf[256];
    snprintf(debug_buf, sizeof(debug_buf), "Begin WebDAV shakehand");
    log_file_write(debug_buf);
    
    // 切换到WebDAV模式（清理BSD套接字，初始化标准套接字）
    log_file_write("Preparing for WebDAV handshake - switching socket mode");
    Result rc = switch_to_webdav_mode();
    if (R_FAILED(rc)) {
        log_file_write("Failed to switch to WebDAV mode");
        return false;
    }
    
    // 等待套接字切换完成
    svcSleepThread(100000000LL); // 100ms
    
    snprintf(debug_buf, sizeof(debug_buf), "WebDAV mode switch completed");
    log_file_write(debug_buf);
    
    // 构造完整的 WebDAV URL（注意末尾斜杠）
    snprintf(url, sizeof(url), "%s/%s/", webdav_config.origin, webdav_config.basepath);
    snprintf(debug_buf, sizeof(debug_buf), "WebDAV URL: %s", url);
    log_file_write(debug_buf);
    
    curl = curl_easy_init();
    if (curl) {
        snprintf(debug_buf, sizeof(debug_buf), "curl initialization successful");
        log_file_write(debug_buf);
        
        char errbuf[CURL_ERROR_SIZE];
        memset(errbuf, 0, sizeof(errbuf));
        curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, errbuf);

        // 目标：WebDAV PROPFIND
        curl_easy_setopt(curl, CURLOPT_URL, url);
        curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, "PROPFIND");
        curl_easy_setopt(curl, CURLOPT_USERAGENT, "libnx-webdav/1.0");

        // Basic 认证（从配置文件读取）
        curl_easy_setopt(curl, CURLOPT_HTTPAUTH, (long)CURLAUTH_BASIC);
        curl_easy_setopt(curl, CURLOPT_USERNAME, webdav_config.username);
        curl_easy_setopt(curl, CURLOPT_PASSWORD, webdav_config.password);

        struct curl_slist *headers = NULL;
        headers = curl_slist_append(headers, "Depth: 0");
        headers = curl_slist_append(headers, "Content-Type: text/xml; charset=\"utf-8\"");
        curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
        
        // 进行DNS解析获取实际IP地址
        struct hostent *host_entry;
        char actual_ip[INET_ADDRSTRLEN];
        // 从webdav_config.origin中提取主机名
        char hostname[128];
        if (strncmp(webdav_config.origin, "http://", 7) == 0) {
            strncpy(hostname, webdav_config.origin + 7, sizeof(hostname) - 1);
        } else if (strncmp(webdav_config.origin, "https://", 8) == 0) {
            strncpy(hostname, webdav_config.origin + 8, sizeof(hostname) - 1);
        } else {
            strncpy(hostname, webdav_config.origin, sizeof(hostname) - 1);
        }
        // 移除路径部分，只保留主机名
        char *path_sep = strchr(hostname, '/');
        if (path_sep) {
            *path_sep = '\0';
        }
        hostname[sizeof(hostname) - 1] = '\0';
        
        host_entry = gethostbyname(hostname);
        if (host_entry != NULL) {
            struct in_addr addr;
            memcpy(&addr, host_entry->h_addr_list[0], sizeof(struct in_addr));
            inet_ntop(AF_INET, &addr, actual_ip, INET_ADDRSTRLEN);
            snprintf(debug_buf, sizeof(debug_buf), "DNS resolution result: %s -> %s", hostname, actual_ip);
            log_file_write(debug_buf);
        } else {
            snprintf(debug_buf, sizeof(debug_buf), "DNS resolution failed: %s", hostname);
            log_file_write(debug_buf);
        }
        
        log_file_write(debug_buf);
        
        // 设置响应数据处理回调函数（修复崩溃问题）
        struct WebDAVResponseData response_data;
        response_data.data = malloc(1);
        if (!response_data.data) {
            snprintf(debug_buf, sizeof(debug_buf), "Failed to allocate memory for response data");
            log_file_write(debug_buf);
            curl_slist_free_all(headers);
            curl_easy_cleanup(curl);
            return false;
        }
        response_data.data[0] = '\0';
        response_data.size = 0;
        
        curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, webdav_response_write_callback);
        curl_easy_setopt(curl, CURLOPT_WRITEDATA, &response_data);
        
        snprintf(debug_buf, sizeof(debug_buf), "libcurl configuration completed");
        log_file_write(debug_buf);
        
        res = curl_easy_perform(curl);
        if (res == CURLE_OK) {
            long code = 0;
            curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &code);
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV PROPFIND completed: status code=%ld", code);
            log_file_write(debug_buf);
            handshake_success = true;
        } else {
            if (errbuf[0]) {
                snprintf(debug_buf, sizeof(debug_buf), "WebDAV request failed: %d, %s", res, errbuf);
                log_file_write(debug_buf);
            } else {
                snprintf(debug_buf, sizeof(debug_buf), "WebDAV request failed, error code: %d", res);
                log_file_write(debug_buf);
            }
        }

        // 清理资源
        snprintf(debug_buf, sizeof(debug_buf), "Cleaning HTTP headers");
        log_file_write(debug_buf);
        curl_slist_free_all(headers);
        curl_easy_cleanup(curl);
        
        // 释放响应数据内存
        if (response_data.data) {
            free(response_data.data);
        }
    } else {
        snprintf(debug_buf, sizeof(debug_buf), "Failed to initialize curl");
        log_file_write(debug_buf);
    }
    
    // 如果握手成功，直接进行流式上传
    if (handshake_success) {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV handshake successful, starting streaming upload");
        log_file_write(debug_buf);
        
        // 获取当前游戏TID
        u64 current_tid = 0;
        if (R_FAILED(get_current_tid(&current_tid)) || current_tid == 0) {
            snprintf(debug_buf, sizeof(debug_buf), "Failed to get current game TID, proceeding with local backup");
            log_file_write(debug_buf);
            handshake_success = false;
            goto cleanup;
        }
        
        // 检查当前游戏用户
        if (g_current_game_user_uid.uid[0] == 0 && g_current_game_user_uid.uid[1] == 0) {
            snprintf(debug_buf, sizeof(debug_buf), "No current game user detected, proceeding with local backup");
            log_file_write(debug_buf);
            handshake_success = false;
            goto cleanup;
        }
        
        // 使用全局变量中的用户信息
        AccountUid target_user = g_current_game_user_uid;
        const char* username = g_current_game_user_name[0] ? g_current_game_user_name : "Unknown";
        
        snprintf(debug_buf, sizeof(debug_buf), "Processing WebDAV upload for user: %s (%016lX%016lX)", 
                 username, target_user.uid[0], target_user.uid[1]);
        log_file_write(debug_buf);
        
        // 获取游戏名称用于构造搜索路径
        char local_folder_name[128] = {0};
        char local_sanitized_name[128] = {0};
        char local_tid_str[32] = {0};
        
        // 尝试从存档生成时使用的TID获取游戏名称
        // 注意：这里我们使用存档生成时的TID，而不是当前TID
        NcmContentId content_id = {0};
        struct AppName app_name = {0};
        
        // 首先尝试从全局变量中获取之前运行的游戏TID
        u64 game_tid = g_previous_game_tid; // 使用全局变量g_previous_game_tid
        if (game_tid == 0x0100000000001000ULL || game_tid == 0) {
            // 如果g_previous_game_tid是QLAUNCH或0，则使用当前TID
            game_tid = current_tid;
        }
        
        if (game_tid != 0 && game_tid != 0x0100000000001000ULL) {
            get_app_en_name(game_tid, &content_id, &app_name);
            
            // 清理游戏名称中的非法字符
            if (strlen(app_name.str) > 0) {
                strncpy(local_sanitized_name, app_name.str, sizeof(local_sanitized_name) - 1);
                sanitize_filename(local_sanitized_name);
                strncpy(local_folder_name, local_sanitized_name, sizeof(local_folder_name) - 1);
                local_folder_name[sizeof(local_folder_name) - 1] = '\0';
            }
            
            // 如果无法获取游戏名称，则使用TID作为后备
            if (strlen(local_sanitized_name) == 0) {
                snprintf(local_tid_str, sizeof(local_tid_str), "%016lX", game_tid);
                strncpy(local_folder_name, local_tid_str, sizeof(local_folder_name) - 1);
                local_folder_name[sizeof(local_folder_name) - 1] = '\0';
            }
        } else {
            // 如果无法获取有效的游戏TID，使用默认名称
            strcpy(local_folder_name, "UnknownGame");
        }
        
        snprintf(debug_buf, sizeof(debug_buf), "Using game folder name: %s for TID %016lX", local_folder_name, game_tid);
        log_file_write(debug_buf);
        
        // 查找本地已生成的ZIP文件
        FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
        if (sdmc_fs == NULL) {
            snprintf(debug_buf, sizeof(debug_buf), "Failed to get SDMC filesystem for finding local backup");
            log_file_write(debug_buf);
            handshake_success = false;
            goto cleanup;
        } else {
            snprintf(debug_buf, sizeof(debug_buf), "Successfully obtained SDMC filesystem in WebDAV mode");
            log_file_write(debug_buf);
        }
        
        // 构造本地存档路径模式：/AutoBack/用户名/local_folder_name
        char search_pattern[FS_MAX_PATH];
        snprintf(search_pattern, sizeof(search_pattern), "%s/%s/%s", AUTOBACK_DIR_PATH, username, local_folder_name);
        
        snprintf(debug_buf, sizeof(debug_buf), "Searching for local backup files in: %s", search_pattern);
        log_file_write(debug_buf);
        
        // 查找最新的ZIP文件
        char latest_zip_path[FS_MAX_PATH] = {0};
        s64 latest_zip_time = 0;
        
        // 遍历目录查找ZIP文件
        FsDir search_dir;
        snprintf(debug_buf, sizeof(debug_buf), "Attempting to open directory: %s", search_pattern);
        log_file_write(debug_buf);
        
        Result dir_rc = fsFsOpenDirectory(sdmc_fs, search_pattern, FsDirOpenMode_ReadDirs | FsDirOpenMode_ReadFiles, &search_dir);
        
        if (R_SUCCEEDED(dir_rc)) {
            snprintf(debug_buf, sizeof(debug_buf), "Successfully opened directory: %s", search_pattern);
            log_file_write(debug_buf);
            s64 entry_count = 0;
            fsDirGetEntryCount(&search_dir, &entry_count);
            
            if (entry_count > 0) {
                snprintf(debug_buf, sizeof(debug_buf), "Directory contains %ld entries", entry_count);
                log_file_write(debug_buf);
                
                // 读取目录条目
                size_t entry_buffer_size = sizeof(FsDirectoryEntry) * entry_count;
                FsDirectoryEntry* entries = malloc(entry_buffer_size);
                if (entries != NULL) {
                    s64 entries_read = 0;
                    Result read_rc = fsDirRead(&search_dir, &entries_read, entry_count, entries);
                    
                    if (R_SUCCEEDED(read_rc) && entries_read > 0) {
                        snprintf(debug_buf, sizeof(debug_buf), "Successfully read %ld entries from directory", entries_read);
                        log_file_write(debug_buf);
                        // 查找最新的ZIP文件
                        for (s64 i = 0; i < entries_read; i++) {
                            snprintf(debug_buf, sizeof(debug_buf), "Found entry: %s (type: %d)", entries[i].name, entries[i].type);
                            log_file_write(debug_buf);
                            
                            if (strstr(entries[i].name, ".zip") != NULL) {
                                snprintf(debug_buf, sizeof(debug_buf), "Found ZIP file: %s", entries[i].name);
                                log_file_write(debug_buf);
                                // 获取文件修改时间
                                FsFile entry_file;
                                char file_path[FS_MAX_PATH];
                                snprintf(file_path, sizeof(file_path), "%s/%s", search_pattern, entries[i].name);
                                snprintf(debug_buf, sizeof(debug_buf), "Attempting to open file: %s", file_path);
                                log_file_write(debug_buf);
                                
                                Result file_rc = fsFsOpenFile(sdmc_fs, file_path, FsOpenMode_Read, &entry_file);
                                if (R_SUCCEEDED(file_rc)) {
                                    snprintf(debug_buf, sizeof(debug_buf), "Successfully opened file: %s", file_path);
                                    log_file_write(debug_buf);
                                    s64 file_size;
                                    fsFileGetSize(&entry_file, &file_size);
                                    
                                    // 简单的文件大小检查作为时间戳替代
                                    if (file_size > latest_zip_time) {
                                        latest_zip_time = file_size;
                                        snprintf(latest_zip_path, sizeof(latest_zip_path), "%s/%s", search_pattern, entries[i].name);
                                    }
                                    
                                    fsFileClose(&entry_file);
                                } else {
                                    snprintf(debug_buf, sizeof(debug_buf), "Failed to open file %s: 0x%x", file_path, file_rc);
                                    log_file_write(debug_buf);
                                }
                            }
                        }
                    } else {
                        snprintf(debug_buf, sizeof(debug_buf), "Failed to read directory entries: read_rc=0x%x, entries_read=%ld", read_rc, entries_read);
                        log_file_write(debug_buf);
                    }
                    
                    free(entries);
                } else {
                    snprintf(debug_buf, sizeof(debug_buf), "Failed to allocate memory for directory entries");
                    log_file_write(debug_buf);
                }
            } else {
                snprintf(debug_buf, sizeof(debug_buf), "Directory is empty: %s", search_pattern);
                log_file_write(debug_buf);
            }
            
            fsDirClose(&search_dir);
        } else {
            snprintf(debug_buf, sizeof(debug_buf), "Failed to open directory %s: 0x%x", search_pattern, dir_rc);
            log_file_write(debug_buf);
        }
        
        if (latest_zip_path[0] != '\0') {
            // 找到本地ZIP文件，执行WebDAV上传
            snprintf(debug_buf, sizeof(debug_buf), "Found local backup file: %s", latest_zip_path);
            log_file_write(debug_buf);
            
                // 在上传前管理WebDAV端存档数量（与本地存档保持一致的时序）
            manage_webdav_backup_count(username, local_folder_name);
            
            // 执行WebDAV上传
            Result upload_rc = stream_zip_to_webdav(latest_zip_path, game_tid, target_user, username);
            
            if (R_FAILED(upload_rc)) {
                snprintf(debug_buf, sizeof(debug_buf), "WebDAV streaming upload failed: 0x%x", upload_rc);
                log_file_write(debug_buf);
                handshake_success = false;
            } else {
                snprintf(debug_buf, sizeof(debug_buf), "WebDAV streaming upload completed successfully");
                log_file_write(debug_buf);
            }
        } else {
            // 未找到本地ZIP文件
            snprintf(debug_buf, sizeof(debug_buf), "No local backup file found for TID %016lX and user %s", game_tid, username);
            log_file_write(debug_buf);
            handshake_success = false;
        }
    }
    
cleanup:
    // 切换回FTP模式（清理标准套接字，重新初始化BSD套接字）
    log_file_write("WebDAV handshake and upload completed - switching back to FTP mode");
    Result switch_rc = switch_to_ftp_mode();
    if (R_FAILED(switch_rc)) {
        log_file_write("Warning: Failed to switch back to FTP mode");
    }
    
    // 等待套接字切换完成
    svcSleepThread(300000000LL); // 增加到300ms，确保套接字切换完成和状态稳定
    
    snprintf(debug_buf, sizeof(debug_buf), "Switched back to FTP mode");
    log_file_write(debug_buf);
    
    // 状态变量已在switch_to_ftp_mode函数中重置，无需重复重置
    log_file_write("WebDAV operation completed, ready to resume game TID monitoring");
    
    // 返回true表示握手和上传都成功，false表示需要本地生成
    return handshake_success;
}

// 创建WebDAV目录的函数
static bool create_webdav_directory(const char* dir_path) {
    CURL* curl = curl_easy_init();
    if (!curl) return false;
    
    // 对目录路径进行URL编码以处理空格等特殊字符
    char encoded_path[256];
    CURL* curl_encode = curl_easy_init();
    if (curl_encode) {
        char* encoded = curl_easy_escape(curl_encode, dir_path, 0);
        if (encoded) {
            strncpy(encoded_path, encoded, sizeof(encoded_path) - 1);
            curl_free(encoded);
        } else {
            strncpy(encoded_path, dir_path, sizeof(encoded_path) - 1);
        }
        curl_easy_cleanup(curl_encode);
    } else {
        strncpy(encoded_path, dir_path, sizeof(encoded_path) - 1);
    }
    
    char mkcol_url[256];
    if (webdav_config.basepath[0] != '\0') {
        // 确保origin和basepath之间有正确的斜杠分隔符
        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/' && webdav_config.basepath[0] == '/') {
            // origin以/结尾，basepath以/开头，移除basepath开头的/
            snprintf(mkcol_url, sizeof(mkcol_url), "%s%s%s/", 
                     webdav_config.origin, webdav_config.basepath + 1, encoded_path);
        } else if (webdav_config.origin[strlen(webdav_config.origin)-1] != '/' && webdav_config.basepath[0] != '/') {
            // origin不以/结尾，basepath不以/开头，添加/
            snprintf(mkcol_url, sizeof(mkcol_url), "%s/%s/%s/", 
                     webdav_config.origin, webdav_config.basepath, encoded_path);
        } else {
            // 其中一个有/，直接拼接
            snprintf(mkcol_url, sizeof(mkcol_url), "%s%s%s/", 
                     webdav_config.origin, webdav_config.basepath, encoded_path);
        }
    } else {
        // 确保origin以/结尾
        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/') {
            snprintf(mkcol_url, sizeof(mkcol_url), "%s%s/", 
                     webdav_config.origin, encoded_path);
        } else {
            snprintf(mkcol_url, sizeof(mkcol_url), "%s/%s/", 
                     webdav_config.origin, encoded_path);
        }
    }
    
    curl_easy_setopt(curl, CURLOPT_URL, mkcol_url);
    curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, "MKCOL");
    curl_easy_setopt(curl, CURLOPT_HTTPAUTH, CURLAUTH_BASIC);
    curl_easy_setopt(curl, CURLOPT_USERNAME, webdav_config.username);
    curl_easy_setopt(curl, CURLOPT_PASSWORD, webdav_config.password);
    
    curl_easy_perform(curl);
    long http_code = 0;
    curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &http_code);
    
    curl_easy_cleanup(curl);
    return (http_code == 201 || http_code == 405); // 201创建成功，405目录已存在
}

// WebDAV数据传输回调
static size_t webdav_response_write_callback(void* ptr, size_t size, size_t nmemb, void* user_data) {
    struct WebDAVResponseData* response = (struct WebDAVResponseData*)user_data;
    size_t total_size = size * nmemb;
    
    // 重新分配内存以容纳新数据
    char* new_data = realloc(response->data, response->size + total_size + 1);
    if (new_data == NULL) {
        return 0; // 内存分配失败
    }
    
    response->data = new_data;
    memcpy(response->data + response->size, ptr, total_size);
    response->size += total_size;
    response->data[response->size] = '\0'; // 确保字符串以null结尾
    
    return total_size;
}

static size_t webdav_upload_read_callback(void* ptr, size_t size, size_t nmemb, void* user_data) {
    struct WebDAVUploadData* upload_data = (struct WebDAVUploadData*)user_data;
    size_t requested_size = size * nmemb;
    
    // 检查是否已读取完文件
    if (upload_data->total_uploaded >= upload_data->file_size) {
        return 0; // 文件读取完毕
    }
    
    // 计算本次可读取的字节数
    size_t remaining = upload_data->file_size - upload_data->total_uploaded;
    size_t bytes_to_read = (requested_size < remaining) ? requested_size : remaining;
    
    // 从本地ZIP文件中读取数据
    size_t bytes_read = 0;
    Result rc = fsFileRead(upload_data->file_handle, upload_data->total_uploaded, ptr, bytes_to_read, 0, &bytes_read);
    if (R_FAILED(rc)) {
        snprintf(upload_data->debug_buf, sizeof(upload_data->debug_buf), "错误: 读取本地ZIP文件时出错: 0x%x", rc);
        log_file_write(upload_data->debug_buf);
        return CURL_READFUNC_ABORT;
    }
    
    upload_data->total_uploaded += bytes_read;
    
    // 移除每MB上传一次的日志，只在开始和完成时输出
    
    return bytes_read;
}

// WebDAV文件操作
static void get_latest_webdav_timestamp_and_sequence(const char* username, const char* folder_name, 
                                                     char* latest_timestamp, size_t timestamp_size, 
                                                     int* sequence_num) {
    log_file_fwrite("[TIMESTAMP_EXTRACT] 开始提取时间戳: username=%s, folder_name=%s", username, folder_name);
    
    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
    if (sdmc_fs == NULL) {
        log_file_fwrite("[TIMESTAMP_EXTRACT] 错误: 无法获取SD卡文件系统");
        return;
    }
    
    char search_pattern[FS_MAX_PATH];
    snprintf(search_pattern, sizeof(search_pattern), "%s/%s/%s", AUTOBACK_DIR_PATH, username, folder_name);
    log_file_fwrite("[TIMESTAMP_EXTRACT] 搜索路径: %s", search_pattern);
    
    FsDir search_dir;
    Result dir_rc = fsFsOpenDirectory(sdmc_fs, search_pattern, FsDirOpenMode_ReadDirs | FsDirOpenMode_ReadFiles, &search_dir);
    
    if (R_FAILED(dir_rc)) {
        log_file_fwrite("[TIMESTAMP_EXTRACT] 错误: 无法打开目录, 结果代码=0x%X, 使用默认时间戳", dir_rc);
        // 设置默认时间戳
        if (latest_timestamp != NULL && timestamp_size > 0) {
            strncpy(latest_timestamp, "0000.00.00@00.00.00", timestamp_size - 1);
            latest_timestamp[timestamp_size - 1] = '\0';
        }
        if (sequence_num != NULL) {
            *sequence_num = 1; // 第一个存档使用序列号1
        }
        return;
    }
    
    s64 entry_count = 0;
    fsDirGetEntryCount(&search_dir, &entry_count);
    log_file_fwrite("[TIMESTAMP_EXTRACT] 目录条目数: %lld", entry_count);
    
    if (entry_count <= 0) {
        log_file_fwrite("[TIMESTAMP_EXTRACT] 目录为空, 使用默认时间戳");
        // 设置默认时间戳
        if (latest_timestamp != NULL && timestamp_size > 0) {
            strncpy(latest_timestamp, "0000.00.00@00.00.00", timestamp_size - 1);
            latest_timestamp[timestamp_size - 1] = '\0';
        }
        if (sequence_num != NULL) {
            *sequence_num = 1; // 第一个存档使用序列号1
        }
        fsDirClose(&search_dir);
        return;
    }
    
    // 读取目录条目
    size_t entry_buffer_size = sizeof(FsDirectoryEntry) * entry_count;
    FsDirectoryEntry* entries = malloc(entry_buffer_size);
    if (entries == NULL) {
        log_file_fwrite("[TIMESTAMP_EXTRACT] 错误: 内存分配失败, 使用默认时间戳");
        // 设置默认时间戳
        if (latest_timestamp != NULL && timestamp_size > 0) {
            strncpy(latest_timestamp, "0000.00.00@00.00.00", timestamp_size - 1);
            latest_timestamp[timestamp_size - 1] = '\0';
        }
        if (sequence_num != NULL) {
            *sequence_num = 1; // 第一个存档使用序列号1
        }
        fsDirClose(&search_dir);
        return;
    }
    
    s64 entries_read = 0;
    Result read_rc = fsDirRead(&search_dir, &entries_read, entry_count, entries);
    
    if (R_FAILED(read_rc) || entries_read <= 0) {
        log_file_fwrite("[TIMESTAMP_EXTRACT] 错误: 读取目录失败, 结果代码=0x%X, 读取条目数=%lld, 使用默认时间戳", read_rc, entries_read);
        // 设置默认时间戳
        if (latest_timestamp != NULL && timestamp_size > 0) {
            strncpy(latest_timestamp, "0000.00.00@00.00.00", timestamp_size - 1);
            latest_timestamp[timestamp_size - 1] = '\0';
        }
        if (sequence_num != NULL) {
            *sequence_num = 1; // 第一个存档使用序列号1
        }
        free(entries);
        fsDirClose(&search_dir);
        return;
    }
    
    log_file_fwrite("[TIMESTAMP_EXTRACT] 成功读取 %lld 目录条目", entries_read);
    
    // 单遍扫描：同时查找最新时间戳和最大序列号
    time_t max_timestamp = 0;
    int max_sequence = 0;
    char max_timestamp_str[64] = {0};
    bool has_zero_timestamp = false; // 标记是否存在全零时间戳
    
    log_file_fwrite("[TIMESTAMP_EXTRACT] 开始单遍扫描: 查找最新时间戳和最大序列号");
    
    for (s64 i = 0; i < entries_read; i++) {
        if (strstr(entries[i].name, ".zip") != NULL) {
            log_file_fwrite("[TIMESTAMP_EXTRACT] 处理文件: %s", entries[i].name);
            
            int sequence = 0;
            time_t timestamp = parse_timestamp_from_filename(entries[i].name, &sequence);
            log_file_fwrite("[TIMESTAMP_EXTRACT] 文件 %s 解析时间戳: %ld, 序列号: %d", entries[i].name, timestamp, sequence);
            
            // 检查是否是全零时间戳
            if (timestamp != 0) {
                // 检查时间戳是否对应全零时间字符串
                char* underscore_pos = strrchr(entries[i].name, '_');
                if (underscore_pos != NULL) {
                    char* time_start = NULL;
                    size_t time_len = 0;
                    
                    // 如果有序列号，找到时间戳部分的开始
                    if (sequence > 0) {
                        char* time_underscore = underscore_pos - 1;
                        while (time_underscore > entries[i].name && *time_underscore != '_') {
                            time_underscore--;
                        }
                        if (time_underscore != entries[i].name && *time_underscore == '_') {
                            time_start = time_underscore + 1;
                            time_len = underscore_pos - time_start;
                        }
                    } else {
                        // 单时间戳格式
                        time_start = underscore_pos + 1;
                        char* zip_ext = strstr(time_start, ".zip");
                        if (zip_ext != NULL) {
                            time_len = zip_ext - time_start;
                        }
                    }
                    
                    if (time_start != NULL && time_len > 0 && time_len < 64) {
                        char time_str[64] = {0};
                        strncpy(time_str, time_start, time_len);
                        time_str[time_len] = '\0';
                        
                        // 检查是否是全零时间戳字符串
                        if (strcmp(time_str, "0000.00.00@00.00.00") == 0) {
                            has_zero_timestamp = true;
                            log_file_fwrite("[TIMESTAMP_EXTRACT] 检测到全零时间戳字符串: %s", time_str);
                        }
                    }
                }
            }
            
            if (timestamp != 0) {
                if (timestamp > max_timestamp || (timestamp < 0 && max_timestamp == 0)) {
                    max_timestamp = timestamp;
                    max_sequence = sequence;
                    log_file_fwrite("[TIMESTAMP_EXTRACT] 发现新最大时间戳: %ld, 序列号: %d", max_timestamp, max_sequence);
                    
                    // 提取时间戳字符串
                    char* underscore_pos = strrchr(entries[i].name, '_');
                    if (underscore_pos != NULL) {
                        // 如果有序列号，找到时间戳部分的开始
                        if (sequence > 0) {
                            char* time_underscore = underscore_pos - 1;
                            while (time_underscore > entries[i].name && *time_underscore != '_') {
                                time_underscore--;
                            }
                            if (time_underscore != entries[i].name && *time_underscore == '_') {
                                char* time_start = time_underscore + 1;
                                size_t time_len = underscore_pos - time_start;
                                if (time_len < sizeof(max_timestamp_str)) {
                                    strncpy(max_timestamp_str, time_start, time_len);
                                    max_timestamp_str[time_len] = '\0';
                                    log_file_fwrite("[TIMESTAMP_EXTRACT] 有序列号格式, 时间: %s", max_timestamp_str);
                                }
                            }
                        } else {
                            // 单时间戳格式
                            char* time_start = underscore_pos + 1;
                            char* zip_ext = strstr(time_start, ".zip");
                            if (zip_ext != NULL) {
                                size_t time_len = zip_ext - time_start;
                                if (time_len < sizeof(max_timestamp_str)) {
                                    strncpy(max_timestamp_str, time_start, time_len);
                                    max_timestamp_str[time_len] = '\0';
                                    log_file_fwrite("[TIMESTAMP_EXTRACT] 单时间戳格式, 时间: %s", max_timestamp_str);
                                }
                            }
                        }
                    }
                } else if (timestamp == max_timestamp && sequence > max_sequence) {
                    // 相同时间戳，更新最大序列号
                    max_sequence = sequence;
                    log_file_fwrite("[TIMESTAMP_EXTRACT] 相同时间戳 %ld, 更新最大序列号: %d", max_timestamp, max_sequence);
                }
            }
        }
    }
    
    // 如果没有找到有效时间戳，使用全0时间戳
    if (max_timestamp == 0) {
        strncpy(max_timestamp_str, "0000.00.00@00.00.00", sizeof(max_timestamp_str) - 1);
        log_file_fwrite("[TIMESTAMP_EXTRACT] 未检测到有效时间戳, 使用默认: %s", max_timestamp_str);
    } else if (max_timestamp < 0) {
        // 如果找到的是全零时间戳（负数），使用原始的全零时间戳字符串
        log_file_fwrite("[TIMESTAMP_EXTRACT] 检测到全零时间戳 (负数), 使用原始字符串: %s", max_timestamp_str);
    } else {
        log_file_fwrite("[TIMESTAMP_EXTRACT] 最终确定的最大时间戳: %s (时间戳=%ld), 最大序列号: %d", max_timestamp_str, max_timestamp, max_sequence);
    }
    
    // 如果存在全零时间戳，并且当前最大时间戳也是全零时间戳，则增加序列号
    if (has_zero_timestamp && strcmp(max_timestamp_str, "0000.00.00@00.00.00") == 0) {
        // 注意：这里不增加序列号，因为函数最后会返回 max_sequence + 1
        log_file_fwrite("[TIMESTAMP_EXTRACT] 检测到全零时间戳, 将使用下一个序列号");
    }
    
    // 返回结果
    if (latest_timestamp != NULL && timestamp_size > 0) {
        strncpy(latest_timestamp, max_timestamp_str, timestamp_size - 1);
        latest_timestamp[timestamp_size - 1] = '\0';
    }
    
    if (sequence_num != NULL) {
        *sequence_num = max_sequence + 1; // 返回下一个序列号
    }
    
    log_file_fwrite("[TIMESTAMP_EXTRACT] 提取完成: 最新时间戳=%s, 序列号=%d", 
                   latest_timestamp ? latest_timestamp : "NULL", sequence_num ? *sequence_num : -1);
    
    free(entries);
    fsDirClose(&search_dir);
    
    log_file_fwrite("[TIMESTAMP_EXTRACT] 函数执行结束");
}

// 添加流式传输ZIP到WebDAV的函数 - 从本地ZIP文件上传
static Result stream_zip_to_webdav(const char* local_zip_path, u64 tid, AccountUid user_uid, const char* username) {
    CURL* curl;
    CURLcode res;
    char url[256];
    Result result = 0;
    FsFile zip_file;
    
    // 参数验证
    if (!local_zip_path || strlen(local_zip_path) == 0) {
        char debug_buf[256] = {0};
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV上传失败, 本地ZIP路径为空");
        log_file_write(debug_buf);
        return -1;
    }
    
    if (!username || strlen(username) == 0) {
        char debug_buf[256] = {0};
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV上传失败, 用户名为空, 使用UID作为后备");
        log_file_write(debug_buf);
        
        // 使用UID作为后备用户名
        static char uid_fallback[64] = {0};
        snprintf(uid_fallback, sizeof(uid_fallback), "%016lX%016lX", 
                 (u64)(user_uid.uid[1]) << 32 | user_uid.uid[0], 
                 (u64)(user_uid.uid[3]) << 32 | user_uid.uid[2]);
        username = uid_fallback;
        
        snprintf(debug_buf, sizeof(debug_buf), "使用UID作为用户名, UID: %s", username);
        log_file_write(debug_buf);
    }
    
    // 添加调试日志：开始WebDAV上传
    char debug_buf[256] = {0};
    snprintf(debug_buf, sizeof(debug_buf), "开始WebDAV上传, TID: %016lX, 用户: %s, 本地文件: %s", tid, username, local_zip_path);
    log_file_write(debug_buf);
    
    // 获取NTP时间戳用于云端存档命名
    time_t ntp_time = get_ntp_time();
    char ntp_timestamp[64];
    
    if (ntp_time == 0) {
        // 如果NTP时间不可用，直接不上传
        char debug_buf[256] = {0};
        snprintf(debug_buf, sizeof(debug_buf), "NTP时间不可用, 跳过WebDAV上传");
        log_file_write(debug_buf);
        create_ultrahand_notification("无法获取时间，备份上传失败", 1);
        NcmContentId content_id = {0};
        struct AppName app_name = {0};
        get_app_log_name(tid, &content_id, &app_name);
        backuplog_fwrite("云端备份失败，仅备份至本地|%s|%s|0000.00.00@00.00.00", app_name.str, username);
        return -1;
    } else {
        // 使用NTP时间戳
        struct tm* tm_info = localtime(&ntp_time);
        strftime(ntp_timestamp, sizeof(ntp_timestamp), "%Y.%m.%d@%H.%M.%S", tm_info);
    }
    
    // 获取游戏标题名称并清理
    char sanitized_title[256] = {0};
    NcmContentId content_id = {0};
    struct AppName app_name = {0};
    
    if (tid != 0 && tid != 0x0100000000001000ULL) {
        get_app_en_name(tid, &content_id, &app_name);
        if (strlen(app_name.str) > 0) {
            strncpy(sanitized_title, app_name.str, sizeof(sanitized_title) - 1);
            sanitize_filename(sanitized_title);
        }
    }
    
    // 如果无法获取游戏名称，使用TID作为后备
    if (strlen(sanitized_title) == 0) {
        snprintf(sanitized_title, sizeof(sanitized_title), "%016lX", tid);
    }
    
    // 清理用户名中的非法字符并验证
    char sanitized_username[256] = {0};
    if (username && strlen(username) > 0) {
        strncpy(sanitized_username, username, sizeof(sanitized_username) - 1);
        sanitize_filename(sanitized_username);
        
        // 验证清理后的用户名是否有效（不为空且包含有效字符）
        bool has_valid_chars = false;
        for (int i = 0; sanitized_username[i] != '\0'; i++) {
            if (isalnum((unsigned char)sanitized_username[i]) || sanitized_username[i] == '_' || sanitized_username[i] == '-') {
                has_valid_chars = true;
                break;
            }
        }
        
        if (!has_valid_chars || strlen(sanitized_username) == 0) {
            char debug_buf[256] = {0};
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV: CURL初始化失败, 使用原始值");
            log_file_write(debug_buf);
            
            // 使用UID作为后备用户名
            snprintf(sanitized_username, sizeof(sanitized_username), "%016lX%016lX", 
                     (u64)(user_uid.uid[1]) << 32 | user_uid.uid[0], 
                     (u64)(user_uid.uid[3]) << 32 | user_uid.uid[2]);
        }
    } else {
        // 用户名为空，使用UID
        snprintf(sanitized_username, sizeof(sanitized_username), "%016lX%016lX", 
                 (u64)(user_uid.uid[1]) << 32 | user_uid.uid[0], 
                 (u64)(user_uid.uid[3]) << 32 | user_uid.uid[2]);
    }
    
    // 对URL组件进行URL编码以处理空格等特殊字符
    char encoded_title[256], encoded_username[256], encoded_ntp_timestamp[128];
    CURL* curl_encode = curl_easy_init();
    if (curl_encode) {
        char* enc_title = curl_easy_escape(curl_encode, sanitized_title, 0);
        char* enc_username = curl_easy_escape(curl_encode, sanitized_username, 0);
        char* enc_ntp_timestamp = curl_easy_escape(curl_encode, ntp_timestamp, 0);
        
        if (enc_title && strlen(enc_title) > 0) {
            strncpy(encoded_title, enc_title, sizeof(encoded_title) - 1);
            encoded_title[sizeof(encoded_title) - 1] = '\0';
        } else {
            strncpy(encoded_title, sanitized_title, sizeof(encoded_title) - 1);
            encoded_title[sizeof(encoded_title) - 1] = '\0';
            char debug_buf[256] = {0};
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV: CURL初始化失败, 使用原始值");
            log_file_write(debug_buf);
        }
        
        if (enc_username && strlen(enc_username) > 0) {
            strncpy(encoded_username, enc_username, sizeof(encoded_username) - 1);
            encoded_username[sizeof(encoded_username) - 1] = '\0';
        } else {
            strncpy(encoded_username, sanitized_username, sizeof(encoded_username) - 1);
            encoded_username[sizeof(encoded_username) - 1] = '\0';
            char debug_buf[256] = {0};
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV: CURL初始化失败, 使用原始值");
            log_file_write(debug_buf);
        }
        
        if (enc_ntp_timestamp && strlen(enc_ntp_timestamp) > 0) {
            strncpy(encoded_ntp_timestamp, enc_ntp_timestamp, sizeof(encoded_ntp_timestamp) - 1);
            encoded_ntp_timestamp[sizeof(encoded_ntp_timestamp) - 1] = '\0';
        } else {
            strncpy(encoded_ntp_timestamp, ntp_timestamp, sizeof(encoded_ntp_timestamp) - 1);
            encoded_ntp_timestamp[sizeof(encoded_ntp_timestamp) - 1] = '\0';
            char debug_buf[256] = {0};
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV: CURL初始化失败, 使用原始值");
            log_file_write(debug_buf);
        }
        
        if (enc_title) curl_free(enc_title);
        if (enc_username) curl_free(enc_username);
        if (enc_ntp_timestamp) curl_free(enc_ntp_timestamp);
        
        curl_easy_cleanup(curl_encode);
    } else {
        // CURL初始化失败，使用原始值
        strncpy(encoded_title, sanitized_title, sizeof(encoded_title) - 1);
        encoded_title[sizeof(encoded_title) - 1] = '\0';
        strncpy(encoded_username, sanitized_username, sizeof(encoded_username) - 1);
        encoded_username[sizeof(encoded_username) - 1] = '\0';
        strncpy(encoded_ntp_timestamp, ntp_timestamp, sizeof(encoded_ntp_timestamp) - 1);
        encoded_ntp_timestamp[sizeof(encoded_ntp_timestamp) - 1] = '\0';
        
        char debug_buf[256] = {0};
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV: CURL初始化失败, 使用原始值");
        log_file_write(debug_buf);
    }
    
    // 构造与本地路径一致的WebDAV上传URL：autoback/{用户名}/{游戏名}/{文件名}.zip
    if (webdav_config.basepath[0] != '\0') {
        // 确保origin和basepath之间有正确的斜杠分隔符
        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/' && webdav_config.basepath[0] == '/') {
            // origin以/结尾，basepath以/开头，移除basepath开头的/
            snprintf(url, sizeof(url), "%s%sAutoBack/%s/%s/%s_%s_%s.zip", 
                     webdav_config.origin, webdav_config.basepath + 1, encoded_username, encoded_title, encoded_title, encoded_username, encoded_ntp_timestamp);
        } else if (webdav_config.origin[strlen(webdav_config.origin)-1] != '/' && webdav_config.basepath[0] != '/') {
            // origin不以/结尾，basepath不以/开头，添加/
            snprintf(url, sizeof(url), "%s/%s/AutoBack/%s/%s/%s_%s_%s.zip", 
                     webdav_config.origin, webdav_config.basepath, encoded_username, encoded_title, encoded_title, encoded_username, encoded_ntp_timestamp);
        } else {
            // 其中一个有/，直接拼接
            snprintf(url, sizeof(url), "%s%sAutoBack/%s/%s/%s_%s_%s.zip", 
                     webdav_config.origin, webdav_config.basepath, encoded_username, encoded_title, encoded_title, encoded_username, encoded_ntp_timestamp);
        }
    } else {
        // 确保origin以/结尾
        if (webdav_config.origin[strlen(webdav_config.origin)-1] == '/') {
            snprintf(url, sizeof(url), "%sAutoBack/%s/%s/%s_%s_%s.zip", 
                     webdav_config.origin, encoded_username, encoded_title, encoded_title, encoded_username, encoded_ntp_timestamp);
        } else {
            snprintf(url, sizeof(url), "%s/AutoBack/%s/%s/%s_%s_%s.zip", 
                     webdav_config.origin, encoded_username, encoded_title, encoded_title, encoded_username, encoded_ntp_timestamp);
        }
    }
    
    snprintf(debug_buf, sizeof(debug_buf), "WebDAV 上传URL: %s", url);
    log_file_write(debug_buf);
    
    // 打开本地ZIP文件
    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
    if (sdmc_fs == NULL) {
        snprintf(debug_buf, sizeof(debug_buf), "获取SDMC文件系统失败");
        log_file_write(debug_buf);
        return -1;
    }
    
    Result rc = fsFsOpenFile(sdmc_fs, local_zip_path, FsOpenMode_Read, &zip_file);
    if (R_FAILED(rc)) {
        snprintf(debug_buf, sizeof(debug_buf), "本地ZIP文件打开失败 %s: 0x%x", local_zip_path, rc);
        log_file_write(debug_buf);
        return -1;
    }
    
    // 获取文件大小
    s64 file_size;
    rc = fsFileGetSize(&zip_file, &file_size);
    if (R_FAILED(rc)) {
        snprintf(debug_buf, sizeof(debug_buf), "获取ZIP大小失败: 0x%x", rc);
        log_file_write(debug_buf);
        fsFileClose(&zip_file);
        return -1;
    }
    
    snprintf(debug_buf, sizeof(debug_buf), "本地ZIP文件打开成功, 大小: %ld 字节", file_size);
    log_file_write(debug_buf);
    
    // 创建autoback格式的WebDAV目录结构：autoback/{用户名}/{游戏名}
    char autoback_game_dir[256];
    
    // 创建autoback基础目录
    if (!create_webdav_directory("AutoBack")) {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 目录创建失败: AutoBack");
        log_file_write(debug_buf);
        // 不返回错误，继续尝试上传
    } else {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 目录已存在或创建成功: AutoBack");
        log_file_write(debug_buf);
    }
    
    // 创建用户目录
    char user_dir[512];
    snprintf(user_dir, sizeof(user_dir), "AutoBack/%s", username);
    if (!create_webdav_directory(user_dir)) {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 目录创建失败: %s", user_dir);
        log_file_write(debug_buf);
        // 不返回错误，继续尝试上传
    } else {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 目录已存在或创建成功: %s", user_dir);
        log_file_write(debug_buf);
    }
    
    // 创建游戏标题目录
    snprintf(autoback_game_dir, sizeof(autoback_game_dir), "AutoBack/%s/%s", username, sanitized_title);
    if (!create_webdav_directory(autoback_game_dir)) {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 目录创建失败: %s", autoback_game_dir);
        log_file_write(debug_buf);
        // 不返回错误，继续尝试上传
    } else {
        snprintf(debug_buf, sizeof(debug_buf), "WebDAV 目录已存在或创建成功: %s", autoback_game_dir);
        log_file_write(debug_buf);
    }
    
    // 初始化CURL
    curl = curl_easy_init();
    if (!curl) {
        snprintf(debug_buf, sizeof(debug_buf), "初始化 WebDAV 上传流失败");
        log_file_write(debug_buf);
        fsFileClose(&zip_file);
        return -1;
    }
    
    // 准备上传数据结构
    struct WebDAVUploadData upload_data = {
        .file_handle = &zip_file,
        .total_uploaded = 0,
        .file_size = file_size,
        .debug_buf = {0}
    };
    
    // 设置CURL选项 - 修复CURL配置冲突
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_UPLOAD, 1L);

    // 设置64KB的CURL缓冲区
    // curl_easy_setopt(curl, CURLOPT_BUFFERSIZE, 65536L);

    // 移除PUT选项，避免与UPLOAD冲突
    // curl_easy_setopt(curl, CURLOPT_PUT, 1L);
    curl_easy_setopt(curl, CURLOPT_READFUNCTION, webdav_upload_read_callback);
    curl_easy_setopt(curl, CURLOPT_READDATA, &upload_data);
    curl_easy_setopt(curl, CURLOPT_USERAGENT, "libnx-webdav-upload/1.0");
    
    // Basic认证
    curl_easy_setopt(curl, CURLOPT_HTTPAUTH, (long)CURLAUTH_BASIC);
    curl_easy_setopt(curl, CURLOPT_USERNAME, webdav_config.username);
    curl_easy_setopt(curl, CURLOPT_PASSWORD, webdav_config.password);
    
    // 设置错误缓冲区
    char errbuf[CURL_ERROR_SIZE];
    memset(errbuf, 0, sizeof(errbuf));
    curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, errbuf);
    
    // 执行上传
    snprintf(debug_buf, sizeof(debug_buf), "开始 WebDAV 上传流...");
    log_file_write(debug_buf);
    
    res = curl_easy_perform(curl);
    
    if (res == CURLE_OK) {
        long http_code = 0;
        curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &http_code);
        
        // 使用get_app_log_name获取游戏名
        NcmContentId content_id = {0};
        struct AppName app_name = {0};
        get_app_log_name(tid, &content_id, &app_name);

        if (http_code == 201 || http_code == 200 || http_code == 204) {
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV 上传成功: HTTP %ld, 已上传字节数: %lu", http_code, upload_data.total_uploaded);
            log_file_write(debug_buf);
            
            // WebDAV上传成功时发送Ultrahand通知
            create_ultrahand_notification("备份上传成功", 1);
            
            // 写入备份记录: "上传成功|游戏名|用户名|时间戳" (2表示WebDAV上传成功)
            backuplog_fwrite("云端备份成功|%s|%s|%s", app_name.str, username, ntp_timestamp);
            
            result = 0;
            
            // 注意：WebDAV存档数量管理已移到上传前执行，与本地存档保持一致时序
        } else {
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV 上传失败: HTTP %ld", http_code);
            log_file_write(debug_buf);
            // WebDAV上传失败时发送Ultrahand通知
            create_ultrahand_notification("备份上传失败", 2);
            
            // 写入备份记录: "上传失败|游戏名|用户名|时间戳" (3表示WebDAV上传失败)
            backuplog_fwrite("云端备份失败，仅备份至本地|%s|%s|%s", app_name.str, username, ntp_timestamp);
            
            result = -1;
        }
    } else {
        if (errbuf[0]) {
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV 上传失败: %d, %s", res, errbuf);
        } else {
            snprintf(debug_buf, sizeof(debug_buf), "WebDAV 上传失败: %d", res);
        }
        log_file_write(debug_buf);
        // WebDAV上传失败时发送Ultrahand通知
        create_ultrahand_notification("备份上传失败", 2);
        
        // 写入备份记录: "上传失败|游戏名|用户名|时间戳" (3表示WebDAV上传失败)
        backuplog_fwrite("云端备份失败，仅备份至本地|%s|%s|%s", sanitized_title, username, ntp_timestamp);
        
        result = -1;
    }
    
    // 清理CURL
    curl_easy_cleanup(curl);
    
    // 关闭ZIP文件
    fsFileClose(&zip_file);
    
    // 如果上传成功，重命名本地ZIP文件为云端命名格式
    if (result == 0) {
        // 等待文件系统完全释放文件
        svcSleepThread(50000000LL); // 50ms
        
        FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
        if (sdmc_fs != NULL) {
            // 构造新的本地文件名：{用户安全昵称}-{日期字符串}.zip
            char new_local_filename[FS_MAX_PATH];
            char new_local_path[FS_MAX_PATH];
            
            // 从URL中提取文件名部分并进行URL解码
            char* filename_start = strrchr(url, '/');
            if (filename_start != NULL) {
                filename_start++; // 跳过'/'
                
                // 使用libcurl进行URL解码
                CURL *curl_tmp = curl_easy_init();
                if (curl_tmp) {
                    char *decoded_filename = curl_easy_unescape(curl_tmp, filename_start, 0, NULL);
                    if (decoded_filename) {
                        strncpy(new_local_filename, decoded_filename, sizeof(new_local_filename) - 1);
                        new_local_filename[sizeof(new_local_filename) - 1] = '\0';
                        curl_free(decoded_filename);
                    } else {
                        strncpy(new_local_filename, filename_start, sizeof(new_local_filename) - 1);
                        new_local_filename[sizeof(new_local_filename) - 1] = '\0';
                    }
                    curl_easy_cleanup(curl_tmp);
                } else {
                    strncpy(new_local_filename, filename_start, sizeof(new_local_filename) - 1);
                    new_local_filename[sizeof(new_local_filename) - 1] = '\0';
                }
                
                // 移除.zip扩展名用于构造路径
                char* zip_ext = strstr(new_local_filename, ".zip");
                if (zip_ext != NULL) {
                    *zip_ext = '\0';
                }
                
                // 构造新的本地文件路径
                char old_filename[FS_MAX_PATH];
                char* old_filename_start = strrchr(local_zip_path, '/');
                if (old_filename_start != NULL) {
                    old_filename_start++; // 跳过'/'
                    strncpy(old_filename, old_filename_start, sizeof(old_filename) - 1);
                    old_filename[sizeof(old_filename) - 1] = '\0';
                    
                    // 构造新路径：保持原有目录结构，只改变文件名
                    char* dir_end = strrchr(local_zip_path, '/');
                    if (dir_end != NULL) {
                        size_t dir_len = dir_end - local_zip_path;
                        strncpy(new_local_path, local_zip_path, dir_len);
                        new_local_path[dir_len] = '\0';
                        strcat(new_local_path, "/");
                        strcat(new_local_path, new_local_filename);
                        strcat(new_local_path, ".zip");
                        
                        // 执行重命名
                        Result rename_rc = fsFsRenameFile(sdmc_fs, local_zip_path, new_local_path);
                        if (R_SUCCEEDED(rename_rc)) {
                            snprintf(debug_buf, sizeof(debug_buf), "本地文件重命名成功: %s -> %s", old_filename, new_local_filename);
                            log_file_write(debug_buf);
                        } else {
                            snprintf(debug_buf, sizeof(debug_buf), "本地文件重命名失败: 0x%x", rename_rc);
                            log_file_write(debug_buf);
                        }
                    }
                }
            }
        }
    }
    
    return result;
}

// ========== 用户界面与通知 ==========

// LED效果控制
void enableBreathingEffect(HidsysUniquePadId unique_pad_id) {
    HidsysNotificationLedPattern pattern;
    memset(&pattern, 0, sizeof(pattern));

    // Setup Breathing effect pattern data.
    pattern.baseMiniCycleDuration = 0x8;             // 100ms.
    pattern.totalMiniCycles = 0x2;                   // 3 mini cycles. Last one 12.5ms.
    pattern.totalFullCycles = 0x0;                   // Repeat forever.
    pattern.startIntensity = 0x2;                    // 13%.

    pattern.miniCycles[0].ledIntensity = 0xF;        // 100%.
    pattern.miniCycles[0].transitionSteps = 0xF;     // 15 steps. Transition time 1.5s.
    pattern.miniCycles[0].finalStepDuration = 0x0;   // Forced 12.5ms.
    pattern.miniCycles[1].ledIntensity = 0x2;        // 13%.
    pattern.miniCycles[1].transitionSteps = 0xF;     // 15 steps. Transition time 1.5s.
    pattern.miniCycles[1].finalStepDuration = 0x0;   // Forced 12.5ms.

    hidsysSetNotificationLedPattern(&pattern, unique_pad_id);
}

void disableBreathingEffect(HidsysUniquePadId unique_pad_id) {
    HidsysNotificationLedPattern pattern;
    memset(&pattern, 0, sizeof(pattern));
    
    // 重复运行3次，确保LED呼吸灯效果被关闭
    for (int i = 0; i < 3; i++) {
        hidsysSetNotificationLedPattern(&pattern, unique_pad_id);
        // 添加短暂延迟，确保每次调用之间有时间间隔
        svcSleepThread(10000000LL); // 10ms
    }
}

void enableHeartbeatEffect(HidsysUniquePadId unique_pad_id) {
    HidsysNotificationLedPattern pattern;
    memset(&pattern, 0, sizeof(pattern));

    // Setup Heartbeat effect pattern data.
    pattern.baseMiniCycleDuration = 0x1;             // 12.5ms.
    pattern.totalMiniCycles = 0xF;                   // 16 mini cycles.
    pattern.totalFullCycles = 0x0;                   // Repeat forever.
    pattern.startIntensity = 0x0;                    // 0%.

    // First beat.
    pattern.miniCycles[0].ledIntensity = 0xF;        // 100%.
    pattern.miniCycles[0].transitionSteps = 0xF;     // 15 steps. Total 187.5ms.
    pattern.miniCycles[0].finalStepDuration = 0x0;   // Forced 12.5ms.
    pattern.miniCycles[1].ledIntensity = 0x0;        // 0%.
    pattern.miniCycles[1].transitionSteps = 0xF;     // 15 steps. Total 187.5ms.
    pattern.miniCycles[1].finalStepDuration = 0x0;   // Forced 12.5ms.

    // Second beat.
    pattern.miniCycles[2].ledIntensity = 0xF;
    pattern.miniCycles[2].transitionSteps = 0xF;
    pattern.miniCycles[2].finalStepDuration = 0x0;
    pattern.miniCycles[3].ledIntensity = 0x0;
    pattern.miniCycles[3].transitionSteps = 0xF;
    pattern.miniCycles[3].finalStepDuration = 0x0;

    // Led off wait time.
    for(int i=2; i<15; i++) {
        pattern.miniCycles[i].ledIntensity = 0x0;        // 0%.
        pattern.miniCycles[i].transitionSteps = 0xF;     // 15 steps. Total 187.5ms.
        pattern.miniCycles[i].finalStepDuration = 0xF;   // 187.5ms.
    }

    hidsysSetNotificationLedPattern(&pattern, unique_pad_id);
}

void disableHeartbeatEffect(HidsysUniquePadId unique_pad_id) {
    HidsysNotificationLedPattern pattern;
    memset(&pattern, 0, sizeof(pattern));
    hidsysSetNotificationLedPattern(&pattern, unique_pad_id);
}

// 显示备份LED效果 - 封装现有的LED开启逻辑
bool Show_Back_LED() {

    // 如果没配置开启，则直接返回
    if (!g_back_led_enabled) return false;

    // 获取手柄设备信息
    HidsysUniquePadId unique_pad_ids[2] = {0};
    s32 total_entries = 0;
    Result rc = hidsysGetUniquePadsFromNpad(HidNpadIdType_No1, unique_pad_ids, 2, &total_entries);
    
    // 尝试手持模式
    if (R_FAILED(rc) || total_entries == 0) {
        rc = hidsysGetUniquePadsFromNpad(HidNpadIdType_Handheld, unique_pad_ids, 2, &total_entries);
    }
      
    // 为所有检测到的手柄开启LED呼吸灯效果
    if (R_SUCCEEDED(rc) && total_entries > 0) {
        for(s32 i = 0; i < total_entries; i++) {
            enableBreathingEffect(unique_pad_ids[i]);
        }
        return true;  // 成功开启至少一个手柄的LED效果
    }
    
    return false;  // 未能开启任何LED效果
}

// 关闭备份LED效果 - 封装现有的LED关闭逻辑
void Close_Back_LED() {

    // 如果没配置开启，则直接返回
    if (!g_back_led_enabled) return;

    // 获取手柄设备信息
    HidsysUniquePadId unique_pad_ids[2] = {0};
    s32 total_entries = 0;
    Result rc = hidsysGetUniquePadsFromNpad(HidNpadIdType_No1, unique_pad_ids, 2, &total_entries);
    
    // 尝试手持模式
    if (R_FAILED(rc) || total_entries == 0) {
        rc = hidsysGetUniquePadsFromNpad(HidNpadIdType_Handheld, unique_pad_ids, 2, &total_entries);
    }
      
    // 为所有检测到的手柄关闭LED呼吸灯效果
    if (R_SUCCEEDED(rc) && total_entries > 0) {
        for(s32 i = 0; i < total_entries; i++) {
            disableBreathingEffect(unique_pad_ids[i]);
        }
    }
}

// Ultrahand通知系统
static void create_ultrahand_notification(const char* message, int priority) {

    // 如果配置文件，没有开启通知，则直接返回
    if (!g_backup_notify_enabled) return;

    char notifications_path[512];
    snprintf(notifications_path, sizeof(notifications_path), "/config/ultrahand/notifications");
    
    // 创建通知目录
    Result rc = createDirectory(notifications_path);
    if (R_FAILED(rc)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "Failed to create ultrahand notifications directory: 0x%x", rc);
        log_file_write(debug_buf);
        return;
    }
    
    // 生成通知文件名
    char notification_file[512];
    time_t now = time(NULL);
    struct tm* tm_info = localtime(&now);
    char timestamp[32];
    strftime(timestamp, sizeof(timestamp), "%Y%m%d_%H%M%S", tm_info);
    snprintf(notification_file, sizeof(notification_file), "%s/%d-%s.notify", notifications_path, priority, timestamp);
    
    // 创建JSON内容
    char json_content[256];
    snprintf(json_content, sizeof(json_content), "{\"text\":\"%s\",\"fontSize\":28}", message);
    
    // 写入通知文件
    rc = createTextFile(notification_file, json_content);
    if (R_FAILED(rc)) {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "Failed to create ultrahand notification file: 0x%x", rc);
        log_file_write(debug_buf);
    } else {
        char debug_buf[256];
        snprintf(debug_buf, sizeof(debug_buf), "Successfully created ultrahand notification: %s", message);
        log_file_write(debug_buf);
    }
}

static Result createDirectory(const char* path) {
    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
    if (sdmc_fs == NULL) {
        return MAKERESULT(Module_Libnx, LibnxError_NotFound);
    }
    
    // 创建多级目录：先创建父目录
    char temp_path[512];
    char* p;
    strncpy(temp_path, path, sizeof(temp_path) - 1);
    temp_path[sizeof(temp_path) - 1] = '\0';
    
    // 跳过开头的 '/'
    p = temp_path;
    if (*p == '/') p++;
    
    while ((p = strchr(p, '/')) != NULL) {
        *p = '\0';
        // 创建当前级别的目录
        Result rc = fsFsCreateDirectory(sdmc_fs, temp_path);
        if (R_FAILED(rc) && rc != 0x402) { // 0x402 = FSERROR_PATH_ALREADY_EXISTS
            // 如果创建失败，尝试继续
        }
        *p = '/';
        p++;
    }
    
    // 创建最终目录
    Result rc = fsFsCreateDirectory(sdmc_fs, path);
    if (R_FAILED(rc) && rc != 0x402) { // 0x402 = FSERROR_PATH_ALREADY_EXISTS
        return rc;
    }
    
    return 0;
}

static Result createTextFile(const char* path, const char* content) {
    FsFileSystem* sdmc_fs = fsdev_wrapGetDeviceFileSystem("sdmc");
    if (sdmc_fs == NULL) {
        return MAKERESULT(Module_Libnx, LibnxError_NotFound);
    }
    
    // 创建文件
    Result rc = fsFsCreateFile(sdmc_fs, path, strlen(content), 0);
    if (R_FAILED(rc) && rc != 0x2EE202) { // 0x2EE202 = FSERROR_PATH_ALREADY_EXISTS
        return rc;
    }
    
    // 打开文件
    FsFile file;
    rc = fsFsOpenFile(sdmc_fs, path, FsOpenMode_Write, &file);
    if (R_FAILED(rc)) {
        return rc;
    }
    
    // 写入内容
    rc = fsFileWrite(&file, 0, content, strlen(content), FsWriteOption_None);
    if (R_FAILED(rc)) {
        fsFileClose(&file);
        return rc;
    }
    
    // 刷新并关闭文件
    fsFileFlush(&file);
    fsFileClose(&file);
    
    return 0;
}

// ========== 工具函数 ==========
// 字符串处理
static void sanitize_filename(char* filename) {
    if (filename == NULL) return;
    
    char* src = filename;
    char* dst = filename;
    bool last_was_underscore = false;
    
    while (*src) {
        // 替换非法字符和空格为下划线
        switch (*src) {
            case '<':
            case '>':
            case ':':
            case '"':
            case '/':
            case '\\':
            case '|':
            case '?':
            case '*':
            case ' ':   // 添加空格处理
            case '\t':  // 添加制表符处理
            case '\n':  // 添加换行符处理
            case '\r':  // 添加回车符处理
                if (!last_was_underscore) {
                    *dst = '_';
                    dst++;
                    last_was_underscore = true;
                }
                break;
            default:
                // 只允许可打印的ASCII字符和常见的Unicode字符
                if ((*src >= 32 && *src <= 126) || (*src & 0x80)) {
                    *dst = *src;
                    dst++;
                    last_was_underscore = false;
                } else if (!last_was_underscore) {
                    *dst = '_';
                    dst++;
                    last_was_underscore = true;
                }
                break;
        }
        src++;
    }
    
    // 移除末尾的下划线、空格和点
    while (dst > filename && (*(dst-1) == '_' || *(dst-1) == ' ' || *(dst-1) == '.')) {
        dst--;
    }
    
    *dst = '\0';
    
    // 确保文件名不为空且不超过合理长度
    if (strlen(filename) == 0) {
        strcpy(filename, "unknown_user");
    } else if (strlen(filename) > 64) {
        // 截断过长的文件名
        filename[64] = '\0';
        // 确保不以下划线结尾
        while (strlen(filename) > 0 && filename[strlen(filename)-1] == '_') {
            filename[strlen(filename)-1] = '\0';
        }
        if (strlen(filename) == 0) {
            strcpy(filename, "truncated_user");
        }
    }
}

// 自定义时间解析函数，替代strptime
static bool custom_strptime(const char* time_str, const char* format, struct tm* tm_info) {
    log_file_fwrite("[CUSTOM_STRPTIME] Starting to parse time string: %s, format: %s", time_str, format);
    
    if (strcmp(format, "%Y %m %d %H:%M:%S") != 0) {
        log_file_fwrite("[CUSTOM_STRPTIME] Error: Unsupported format: %s", format);
        return false;
    }
    
    int year, month, day, hour, minute, second;
    
    // 尝试两种格式：空格分隔和冒号分隔
    int result = sscanf(time_str, "%d %d %d %d:%d:%d", &year, &month, &day, &hour, &minute, &second);
    if (result != 6) {
        // 如果空格分隔失败，尝试冒号分隔
        result = sscanf(time_str, "%d:%d:%d %d:%d:%d", &year, &month, &day, &hour, &minute, &second);
        if (result != 6) {
            log_file_fwrite("[CUSTOM_STRPTIME] Error: sscanf parsing failed, result code: %d", result);
            return false;
        }
        log_file_fwrite("[CUSTOM_STRPTIME] Parsed successfully using colon-separated format");
    } else {
        log_file_fwrite("[CUSTOM_STRPTIME] Parsed successfully using space-separated format");
    }
    
    // 验证时间值的合理性
    if (year < 1900 || year > 2100 || month < 1 || month > 12 || day < 1 || day > 31 ||
        hour < 0 || hour > 23 || minute < 0 || minute > 59 || second < 0 || second > 59) {
        // 特殊处理全零时间戳（视为最旧时间戳）
        if (year == 0 && month == 0 && day == 0 && hour == 0 && minute == 0 && second == 0) {
            log_file_fwrite("[CUSTOM_STRPTIME] Detected all-zero timestamp, treating as oldest valid timestamp");
            tm_info->tm_year = 0; // 1900年
            tm_info->tm_mon = 0;  // 1月
            tm_info->tm_mday = 1; // 1日
            tm_info->tm_hour = 0; // 0时
            tm_info->tm_min = 0;  // 0分
            tm_info->tm_sec = 0;  // 0秒
            tm_info->tm_isdst = -1; // 让mktime自动判断夏令时
            
            log_file_fwrite("[CUSTOM_STRPTIME] All-zero timestamp processed: tm_year=%d, tm_mon=%d, tm_mday=%d, tm_hour=%d, tm_min=%d, tm_sec=%d", 
                           tm_info->tm_year, tm_info->tm_mon, tm_info->tm_mday, tm_info->tm_hour, tm_info->tm_min, tm_info->tm_sec);
            return true;
        }
        
        log_file_fwrite("[CUSTOM_STRPTIME] Error: Invalid time values: year=%d, month=%d, day=%d, hour=%d, minute=%d, second=%d", 
                       year, month, day, hour, minute, second);
        return false;
    }
    
    tm_info->tm_year = year - 1900;
    tm_info->tm_mon = month - 1;
    tm_info->tm_mday = day;
    tm_info->tm_hour = hour;
    tm_info->tm_min = minute;
    tm_info->tm_sec = second;
    tm_info->tm_isdst = -1; // 让mktime自动判断夏令时
    
    log_file_fwrite("[CUSTOM_STRPTIME] Parsing successful: tm_year=%d, tm_mon=%d, tm_mday=%d, tm_hour=%d, tm_min=%d, tm_sec=%d", 
                   tm_info->tm_year, tm_info->tm_mon, tm_info->tm_mday, tm_info->tm_hour, tm_info->tm_min, tm_info->tm_sec);
    
    return true;
}

// 简单的URL解码函数，处理常见的URL编码字符
static void url_decode(char* str) {
    char* src = str;
    char* dst = str;
    
    while (*src) {
        if (*src == '%' && *(src+1) && *(src+2)) {
            // 处理%编码
            char hex[3] = {*(src+1), *(src+2), 0};
            char decoded = (char)strtol(hex, NULL, 16);
            *dst++ = decoded;
            src += 3;
        } else {
            *dst++ = *src++;
        }
    }
    *dst = '\0';
}

// 系统工具
static u32 socketSelectVersion(void) {
    if (hosversionBefore(3,0,0)) {
        return 1;
    } else if (hosversionBefore(4,0,0)) {
        return 2;
    } else if (hosversionBefore(5,0,0)) {
        return 3;
    } else if (hosversionBefore(6,0,0)) {
        return 4;
    } else if (hosversionBefore(8,0,0)) {
        return 5;
    } else if (hosversionBefore(9,0,0)) {
        return 6;
    } else if (hosversionBefore(13,0,0)) {
        return 7;
    } else if (hosversionBefore(16,0,0)) {
        return 8;
    } else /* latest known version */ {
        return 9;
    }
}

 
