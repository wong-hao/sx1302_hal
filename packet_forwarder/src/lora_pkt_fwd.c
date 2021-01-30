/*
 / _____)             _              | |
( (____  _____ ____ _| |_ _____  ____| |__
 \____ \| ___ |    (_   _) ___ |/ ___)  _ \
 _____) ) ____| | | || |_| ____( (___| | | |
(______/|_____)_|_|_| \__)_____)\____)_| |_|
  (C)2019 Semtech

Description:
    Configure Lora concentrator and forward packets to a server
    Use GPS for packet timestamping.
    Send a becon at a regular interval without server intervention

License: Revised BSD License, see LICENSE.TXT file include in the project
*/


/* -------------------------------------------------------------------------- */
/* --- DEPENDANCIES --------------------------------------------------------- */

/* fix an issue between POSIX and C99 */
#if __STDC_VERSION__ >= 199901L
    #define _XOPEN_SOURCE 600
#else
    #define _XOPEN_SOURCE 500
#endif

#include <stdint.h>         /* C99 types */
#include <stdbool.h>        /* bool type */
#include <stdio.h>          /* printf, fprintf, snprintf, fopen, fputs */
#include <inttypes.h>       /* PRIx64, PRIu64... */

#include <string.h>         /* memset */
#include <signal.h>         /* sigaction */
#include <time.h>           /* time, clock_gettime, strftime, gmtime */
#include <sys/time.h>       /* timeval */
#include <unistd.h>         /* getopt, access */
#include <stdlib.h>         /* atoi, exit */
#include <errno.h>          /* error messages */
#include <math.h>           /* modf */

#include <sys/socket.h>     /* socket specific definitions */
#include <netinet/in.h>     /* INET constants and stuff */
#include <arpa/inet.h>      /* IP address conversion stuff */
#include <netdb.h>          /* gai_strerror */

#include <pthread.h>

#include "trace.h" //.. / packet_forwarder / inc / trace.h
#include "jitqueue.h" //.. / packet_forwarder / src / jitqueue.c
#include "parson.h" //.. / libtools / src / parson.c
#include "base64.h" //.. / libtools / src / base64.c
#include "loragw_hal.h" //.. / libloragw / src / loragw_hal.c
#include "loragw_aux.h" //.. / libloragw / src / loragw_aux.c
#include "loragw_reg.h" //.. / libloragw / src / loragw_reg.c
#include "loragw_gps.h" //.. / libloragw / src / loragw_gps.c

/* -------------------------------------------------------------------------- */
/* --- PRIVATE MACROS ------------------------------------------------------- */

#define ARRAY_SIZE(a)   (sizeof(a) / sizeof((a)[0]))
#define STRINGIFY(x)    #x
#define STR(x)          STRINGIFY(x)

#define RAND_RANGE(min, max) (rand() % (max + 1 - min) + min)

/* -------------------------------------------------------------------------- */
/* --- PRIVATE CONSTANTS ---------------------------------------------------- */

#ifndef VERSION_STRING
    #define VERSION_STRING "undefined"
#endif

#define JSON_CONF_DEFAULT   "global_conf.json"

#define DEFAULT_SERVER      127.0.0.1   /* hostname also supported */
#define DEFAULT_PORT_UP     1780
#define DEFAULT_PORT_DW     1782
#define DEFAULT_KEEPALIVE   5           /* default time interval for downstream keep-alive packet */
#define DEFAULT_STAT        30          /* default time interval for statistics */
#define PUSH_TIMEOUT_MS     100
#define PULL_TIMEOUT_MS     200
#define GPS_REF_MAX_AGE     30          /* maximum admitted delay in seconds of GPS loss before considering latest GPS sync unusable */
#define FETCH_SLEEP_MS      10          /* nb of ms waited when a fetch return no packets */
#define BEACON_POLL_MS      50          /* time in ms between polling of beacon TX status */

#define PROTOCOL_VERSION    2           /* v1.6 */
#define PROTOCOL_JSON_RXPK_FRAME_FORMAT 1

#define XERR_INIT_AVG       16          /* nb of measurements the XTAL correction is averaged on as initial value */
#define XERR_FILT_COEF      256         /* coefficient for low-pass XTAL error tracking */

//PROTOCOL packet identifier 标识符
#define PKT_PUSH_DATA   0 //PUSH_DATA packet
#define PKT_PUSH_ACK    1 //PUSH_ACK packet
#define PKT_PULL_DATA   2 //PULL_DATA packet 
#define PKT_PULL_RESP   3 //PULL_RESP packet
#define PKT_PULL_ACK    4 //PULL_ACK packet
#define PKT_TX_ACK      5 //TX_ACK packet

#define NB_PKT_MAX      255 /* max number of packets per fetch/send cycle */

#define MIN_LORA_PREAMB 6 /* minimum Lora preamble length for this application */
#define STD_LORA_PREAMB 8
#define MIN_FSK_PREAMB  3 /* minimum FSK preamble length for this application */
#define STD_FSK_PREAMB  5

#define STATUS_SIZE     200
#define TX_BUFF_SIZE    ((540 * NB_PKT_MAX) + 30 + STATUS_SIZE)
#define ACK_BUFF_SIZE   64

#define UNIX_GPS_EPOCH_OFFSET 315964800 /* Number of seconds ellapsed between 01.Jan.1970 00:00:00
                                                                          and 06.Jan.1980 00:00:00 */ //UTC与GPS时间的差值

//'Beaconing parameters' in 'global.config'，如果global里面没有参数则默认使用这些
#define DEFAULT_BEACON_FREQ_HZ      869525000
#define DEFAULT_BEACON_FREQ_NB      1
#define DEFAULT_BEACON_FREQ_STEP    0
#define DEFAULT_BEACON_DATARATE     9
#define DEFAULT_BEACON_BW_HZ        125000
#define DEFAULT_BEACON_POWER        14
#define DEFAULT_BEACON_INFODESC     0

/* -------------------------------------------------------------------------- */
/* --- PRIVATE TYPES -------------------------------------------------------- */

/* spectral scan */
typedef struct spectral_scan_s {
    bool enable;            /* enable spectral scan thread */
    uint32_t freq_hz_start; /* first channel frequency, in Hz */
    uint8_t nb_chan;        /* number of channels to scan (200kHz between each channel) */
    uint16_t nb_scan;       /* number of scan points for each frequency scan */
    uint32_t pace_s;        /* number of seconds between 2 scans in the thread */
} spectral_scan_t;

/* -------------------------------------------------------------------------- */
/* --- PRIVATE VARIABLES (GLOBAL) ------------------------------------------- */

/* signal handling variables */
volatile bool exit_sig = false; /* 1 -> application terminates cleanly (shut down hardware, close open files, etc) */
volatile bool quit_sig = false; /* 1 -> application terminates without shutting down the hardware */

/* packets filtering configuration variables */ //包过滤，parse_gateway_configuration中求得
static bool fwd_valid_pkt = true; /* packets with PAYLOAD CRC OK are forwarded */
static bool fwd_error_pkt = false; /* packets with PAYLOAD CRC ERROR are NOT forwarded */
static bool fwd_nocrc_pkt = false; /* packets with NO PAYLOAD CRC are NOT forwarded */

/* network configuration variables */ //网络配置，parse_gateway_configuration求得
static uint64_t lgwm = 0; /* Lora gateway MAC address */
static char serv_addr[64] = STR(DEFAULT_SERVER); /* address of the server (host name or IPv4/IPv6) */
static char serv_port_up[8] = STR(DEFAULT_PORT_UP); /* server port for upstream traffic */
static char serv_port_down[8] = STR(DEFAULT_PORT_DW); /* server port for downstream traffic */
static int keepalive_time = DEFAULT_KEEPALIVE; /* send a PULL_DATA request every X seconds, negative = disabled */

/* statistics collection configuration variables */ //统计，parse_gateway_configuration求得
static unsigned stat_interval = DEFAULT_STAT; /* time interval (in sec) at which statistics are collected and displayed */

/* gateway <-> MAC protocol variables */ //main求得
static uint32_t net_mac_h; /* Most Significant Nibble, network order */ //前半字节
static uint32_t net_mac_l; /* Least Significant Nibble, network order */ //后半字节

/* network sockets */ //套接字，main求得
static int sock_up; /* socket for upstream traffic */
static int sock_down; /* socket for downstream traffic */

/* network protocol variables */
static struct timeval push_timeout_half = {0, (PUSH_TIMEOUT_MS * 500)}; /* cut in half, critical for throughput */ //parse_gateway_configuration求得
static struct timeval pull_timeout = {0, (PULL_TIMEOUT_MS * 1000)}; /* non critical for throughput */

/* hardware access control and correction */ //硬件接入，thread_valid求得
pthread_mutex_t mx_concent = PTHREAD_MUTEX_INITIALIZER; /* control access to the concentrator */ //Concentrator
static pthread_mutex_t mx_xcorr = PTHREAD_MUTEX_INITIALIZER; /* control access to the XTAL correction */ //外部晶振
static bool xtal_correct_ok = false; /* set true when XTAL correction is stable enough */
static double xtal_correct = 1.0;

/* GPS configuration and synchronization */ //GPS配置
static char gps_tty_path[64] = "\0"; /* path of the TTY port GPS is connected on */  //parse_gateway_configuration求得，网关是否启用gps的唯一标准（TTY: 硬件终端设备）
static int gps_tty_fd = -1; /* file descriptor of the GPS TTY port */ //main求得
static bool gps_enabled = false; /* is GPS enabled on that gateway ? */ //main求得

/* GPS time reference */
static pthread_mutex_t mx_timeref = PTHREAD_MUTEX_INITIALIZER; /* control access to GPS time reference */
static bool gps_ref_valid; /* is GPS reference acceptable (ie. not too old) */
static struct tref time_reference_gps; /* time reference used for GPS <-> timestamp conversion */

/* Reference coordinates, for broadcasting (beacon) */
static struct coord_s reference_coord;

/* Enable faking the GPS coordinates of the gateway */ //伪造虚假GPS，parse_gateway_configuration求得
static bool gps_fake_enable; /* enable the feature */

/* measurements to establish statistics */ //统计信息，thread_up求得
static pthread_mutex_t mx_meas_up = PTHREAD_MUTEX_INITIALIZER; /* control access to the upstream measurements */
static uint32_t meas_nb_rx_rcv = 0; /* count packets received */
static uint32_t meas_nb_rx_ok = 0; /* count packets received with PAYLOAD CRC OK */
static uint32_t meas_nb_rx_bad = 0; /* count packets received with PAYLOAD CRC ERROR */
static uint32_t meas_nb_rx_nocrc = 0; /* count packets received with NO PAYLOAD CRC */
static uint32_t meas_up_pkt_fwd = 0; /* number of radio packet forwarded to the server */
static uint32_t meas_up_network_byte = 0; /* sum of UDP bytes sent for upstream traffic */
static uint32_t meas_up_payload_byte = 0; /* sum of radio payload bytes sent for upstream traffic */
static uint32_t meas_up_dgram_sent = 0; /* number of datagrams sent for upstream traffic */
static uint32_t meas_up_ack_rcv = 0; /* number of datagrams acknowledged for upstream traffic */

static pthread_mutex_t mx_meas_dw = PTHREAD_MUTEX_INITIALIZER; /* control access to the downstream measurements */

//thread_down求得
//PULL_DATA
static uint32_t meas_dw_pull_sent = 0; /* number of PULL requests sent for downstream traffic */
//PULL_ACK
static uint32_t meas_dw_ack_rcv = 0; /* number of PULL requests acknowledged for downstream traffic */
//PULL_RESP
static uint32_t meas_dw_dgram_rcv = 0; /* count PULL response packets received for downstream traffic */
static uint32_t meas_dw_network_byte = 0; /* sum of UDP bytes sent for upstream traffic */
static uint32_t meas_dw_payload_byte = 0; /* sum of radio payload bytes sent for upstream traffic */

//thread_jit求得
static uint32_t meas_nb_tx_ok = 0; /* count packets emitted successfully */
static uint32_t meas_nb_tx_fail = 0; /* count packets were TX failed for other reasons */

//thread_down求得
//jit_enqueue CLASS A/B/C
static uint32_t meas_nb_tx_requested = 0; /* count TX request from server (downlinks) */

//send_tx_ack求得
static uint32_t meas_nb_tx_rejected_collision_packet = 0; /* count packets were TX request were rejected due to collision with another packet already programmed */
static uint32_t meas_nb_tx_rejected_collision_beacon = 0; /* count packets were TX request were rejected due to collision with a beacon already programmed */
static uint32_t meas_nb_tx_rejected_too_late = 0; /* count packets were TX request were rejected because it is too late to program it */
static uint32_t meas_nb_tx_rejected_too_early = 0; /* count packets were TX request were rejected because timestamp is too much in advance */

//thread_down求得
//jit_enqueue BEACON
static uint32_t meas_nb_beacon_queued = 0; /* count beacon inserted in jit queue */

//thread_jit求得
static uint32_t meas_nb_beacon_sent = 0; /* count beacon actually sent to concentrator */

//thread_down求得
static uint32_t meas_nb_beacon_rejected = 0; /* count beacon rejected for queuing */

//gps_process_coords求得
static pthread_mutex_t mx_meas_gps = PTHREAD_MUTEX_INITIALIZER; /* control access to the GPS statistics */
static bool gps_coord_valid; /* could we get valid GPS coordinates ? */
static struct coord_s meas_gps_coord; /* GPS position of the gateway */
static struct coord_s meas_gps_err; /* GPS position of the gateway */

//main求得
static pthread_mutex_t mx_stat_rep = PTHREAD_MUTEX_INITIALIZER; /* control access to the status report */
static bool report_ready = false; /* true when there is a new report to send to the server */
//main求得，thread_up发送
static char status_report[STATUS_SIZE]; /* status report as a JSON object */

/* beacon parameters */ //class B beacon信标参数，parse_gateway_configuration求得
static uint32_t beacon_period = 0; /* set beaconing period, must be a sub-multiple of 86400, the nb of sec in a day */
static uint32_t beacon_freq_hz = DEFAULT_BEACON_FREQ_HZ; /* set beacon TX frequency, in Hz */
static uint8_t beacon_freq_nb = DEFAULT_BEACON_FREQ_NB; /* set number of beaconing channels beacon */
static uint32_t beacon_freq_step = DEFAULT_BEACON_FREQ_STEP; /* set frequency step between beacon channels, in Hz */
static uint8_t beacon_datarate = DEFAULT_BEACON_DATARATE; /* set beacon datarate (SF) */
static uint32_t beacon_bw_hz = DEFAULT_BEACON_BW_HZ; /* set beacon bandwidth, in Hz */
static int8_t beacon_power = DEFAULT_BEACON_POWER; /* set beacon TX power, in dBm */
static uint8_t beacon_infodesc = DEFAULT_BEACON_INFODESC; /* set beacon information descriptor */

/* auto-quit function */ //自动退出程序，已禁用，parse_gateway_configuration求得
static uint32_t autoquit_threshold = 0; /* enable auto-quit after a number of non-acknowledged PULL_DATA (0 = disabled)*/

/* Just In Time TX scheduling */
static struct jit_queue_s jit_queue[LGW_RF_CHAIN_NB];

/* Gateway specificities */
static int8_t antenna_gain = 0;

/* TX capabilities */ //parse_SX130x_configuration求得；是concentrator用于发射的线路
static struct lgw_tx_gain_lut_s txlut[LGW_RF_CHAIN_NB]; /* TX gain table */ //txlut[i]代指SX130x_conf.radio_%i.tx_gain_lut对象 snprintf(param_name, sizeof param_name, "radio_%i.tx_gain_lut", i);
static uint32_t tx_freq_min[LGW_RF_CHAIN_NB]; /* lowest frequency supported by TX chain */
static uint32_t tx_freq_max[LGW_RF_CHAIN_NB]; /* highest frequency supported by TX chain */
static bool tx_enable[LGW_RF_CHAIN_NB] = {false}; /* Is TX enabled for a given RF chain ? */

//thread_up求得
static uint32_t nb_pkt_log[LGW_IF_CHAIN_NB][8]; /* [CH][SF] */
static uint32_t nb_pkt_received_lora = 0;
static uint32_t nb_pkt_received_fsk = 0;

//parse_debug_configuration中求得
static struct lgw_conf_debug_s debugconf; //debugconf指代debug_conf对象
static uint32_t nb_pkt_received_ref[16]; //global count

/* Interface type */
static lgw_com_type_t com_type = LGW_COM_SPI;

/* Spectral Scan */
static spectral_scan_t spectral_scan_params = {
    .enable = false,
    .freq_hz_start = 0,
    .nb_chan = 0,
    .nb_scan = 0,
    .pace_s = 10
};

/* -------------------------------------------------------------------------- */
/* --- PRIVATE FUNCTIONS DECLARATION ---------------------------------------- */ //函数声明

static void usage(void);

static void sig_handler(int sigio);

static int parse_SX130x_configuration(const char * conf_file);

static int parse_gateway_configuration(const char * conf_file);

static int parse_debug_configuration(const char * conf_file);

static uint16_t crc16(const uint8_t * data, unsigned size);

static double difftimespec(struct timespec end, struct timespec beginning);

static void gps_process_sync(void);

static void gps_process_coords(void);

static int get_tx_gain_lut_index(uint8_t rf_chain, int8_t rf_power, uint8_t * lut_index);

/* threads */ //主函数生成六种线程以管理上游和下游、GPS和频谱扫描
void thread_up(void);
void thread_down(void);
void thread_jit(void);
void thread_gps(void);
void thread_valid(void);
void thread_spectral_scan(void);

/* -------------------------------------------------------------------------- */
/* --- PRIVATE FUNCTIONS DEFINITION ----------------------------------------- */

static void usage( void ) //与命令行有关
{
    printf("~~~ Library version string~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    printf(" %s\n", lgw_version_info()); //用于标识编译后的库版本/选项
    printf("~~~ Available options ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    printf(" -h  print this help\n");
    printf(" -c <filename>  use config file other than 'global_conf.json'\n");
    printf("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
	//pi@raspberrypi:~/gw1302s/bin $ ./lora_pkt_fwd -h
	//~~~ Library version string~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
	//Version: 2.0.1;
	//~~~ Available options ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
	//-h  print this help
	//-c <filename>	use config file other than 'global_conf.json'
	//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~	
}

static void sig_handler(int sigio) { //判断退出程序方法
    if (sigio == SIGQUIT) { //未关闭硬件
        quit_sig = true;
    } else if ((sigio == SIGINT) || (sigio == SIGTERM)) { //正确退出
        exit_sig = true;
    }
    return;
}

static int parse_SX130x_configuration(const char * conf_file) {
    int i, j, number;
    char param_name[32]; /* used to generate variable parameter names */ //作为中间变量
    const char *str; /* used to store string value from JSON object */
    const char conf_obj_name[] = "SX130x_conf";
    JSON_Value *root_val = NULL;
    JSON_Value *val = NULL;
    JSON_Object *conf_obj = NULL; //conf_obj即SX130x_conf
    JSON_Object *conf_txgain_obj;
    JSON_Object *conf_ts_obj;
    JSON_Object *conf_sx1261_obj = NULL;
    JSON_Object *conf_scan_obj = NULL;
    JSON_Object *conf_lbt_obj = NULL;
    JSON_Object *conf_lbtchan_obj = NULL;
    JSON_Array *conf_txlut_array = NULL;
    JSON_Array *conf_lbtchan_array = NULL;
    JSON_Array *conf_demod_array = NULL;

    struct lgw_conf_board_s boardconf; //boardconf指代SX130x_conf对象
    struct lgw_conf_rxrf_s rfconf; //rfconf指代SX130x_conf.radio_%i对象
    struct lgw_conf_rxif_s ifconf; //ifconf指代SX130x_conf.chan_multiSF_i/SX130x_conf.chan_Lora_std/SX130x_conf.chan_FSK对象
    struct lgw_conf_demod_s demodconf; //demodconf指代SX130x_conf.chan_multiSF_All对象
    struct lgw_conf_ftime_s tsconf; //tsconf指代SX130x_conf.fine_timestamp对象
    struct lgw_conf_sx1261_s sx1261conf;
    uint32_t sf, bw, fdev;
    bool sx1250_tx_lut;
    size_t size;

    /* try to parse JSON */ //判断是否是JSON文件
    root_val = json_parse_file_with_comments(conf_file);
    if (root_val == NULL) {
        MSG("ERROR: %s is not a valid JSON file\n", conf_file);
        exit(EXIT_FAILURE);
    }

    /* point to the gateway configuration object */ //判断json文件中是否有SX130x_conf对象
    conf_obj = json_object_get_object(json_value_get_object(root_val), conf_obj_name);
    if (conf_obj == NULL) {
        MSG("INFO: %s does not contain a JSON object named %s\n", conf_file, conf_obj_name);
        return -1;
    } else {
        MSG("INFO: %s does contain a JSON object named %s, parsing SX1302 parameters\n", conf_file, conf_obj_name);
    }

    /* set board configuration */
    memset(&boardconf, 0, sizeof boardconf); /* initialize configuration structure */ //boardconf指代SX130x_conf对象
    str = json_object_get_string(conf_obj, "com_type"); //SX130x_conf.com_type
    if (str == NULL) {
        MSG("ERROR: com_type must be configured in %s\n", conf_file);
        return -1;
    } else if (!strncmp(str, "SPI", 3) || !strncmp(str, "spi", 3)) { //"com_type": "SPI"
        boardconf.com_type = LGW_COM_SPI;
    } else if (!strncmp(str, "USB", 3) || !strncmp(str, "usb", 3)) {
        boardconf.com_type = LGW_COM_USB;
    } else {
        MSG("ERROR: invalid com type: %s (should be SPI or USB)\n", str);
        return -1;
    }
    com_type = boardconf.com_type;
    str = json_object_get_string(conf_obj, "com_path"); //SX130x_conf.com_path
    if (str != NULL) {
        strncpy(boardconf.com_path, str, sizeof boardconf.com_path);
        boardconf.com_path[sizeof boardconf.com_path - 1] = '\0'; /* ensure string termination */
    } else {
        MSG("ERROR: com_path must be configured in %s\n", conf_file);
        return -1;
    }
    val = json_object_get_value(conf_obj, "lorawan_public"); /* fetch value (if possible) */ //boardconf.lorawan_public
    if (json_value_get_type(val) == JSONBoolean) {
        boardconf.lorawan_public = (bool)json_value_get_boolean(val);
    } else {
        MSG("WARNING: Data type for lorawan_public seems wrong, please check\n");
        boardconf.lorawan_public = false;
    }
    val = json_object_get_value(conf_obj, "clksrc"); /* fetch value (if possible) */ //boardconf.clksrc
    if (json_value_get_type(val) == JSONNumber) {
        boardconf.clksrc = (uint8_t)json_value_get_number(val);
    } else {
        MSG("WARNING: Data type for clksrc seems wrong, please check\n");
        boardconf.clksrc = 0;
    }
    val = json_object_get_value(conf_obj, "full_duplex"); /* fetch value (if possible) */ //boardconf.full_duplex
    if (json_value_get_type(val) == JSONBoolean) {
        boardconf.full_duplex = (bool)json_value_get_boolean(val);
    } else {
        MSG("WARNING: Data type for full_duplex seems wrong, please check\n");
        boardconf.full_duplex = false;
    }
    MSG("INFO: com_type %s, com_path %s, lorawan_public %d, clksrc %d, full_duplex %d\n", (boardconf.com_type == LGW_COM_SPI) ? "SPI" : "USB", boardconf.com_path, boardconf.lorawan_public, boardconf.clksrc, boardconf.full_duplex);
    /* all parameters parsed, submitting configuration to the HAL */ //to set the configuration of the concentrator (sx1302)
    if (lgw_board_setconf(&boardconf) != LGW_HAL_SUCCESS) {
        MSG("ERROR: Failed to configure board\n");
        return -1;
    }

    /* set antenna gain configuration */
    val = json_object_get_value(conf_obj, "antenna_gain"); /* fetch value (if possible) */ //antenna_gain
    if (val != NULL) {
        if (json_value_get_type(val) == JSONNumber) {
            antenna_gain = (int8_t)json_value_get_number(val);
        } else {
            MSG("WARNING: Data type for antenna_gain seems wrong, please check\n");
            antenna_gain = 0;
        }
    }
    MSG("INFO: antenna_gain %d dBi\n", antenna_gain);

    /* set timestamp configuration */ ////判断SX130x_conf对象中是否有fine_timestamp对象
    conf_ts_obj = json_object_get_object(conf_obj, "fine_timestamp"); //conf_obj即SX130x_conf
    if (conf_ts_obj == NULL) {
        MSG("INFO: %s does not contain a JSON object for fine timestamp\n", conf_file);
    } else {
        val = json_object_get_value(conf_ts_obj, "enable"); /* fetch value (if possible) */  //tsconf.nable_precision_ts，判断SX130x_conf.fine_timestamp是否启用
        if (json_value_get_type(val) == JSONBoolean) {
            tsconf.enable = (bool)json_value_get_boolean(val); //tsconf指代SX130x_conf.fine_timestamp对象
        } else {
            MSG("WARNING: Data type for fine_timestamp.enable seems wrong, please check\n");
            tsconf.enable = false;
        }
        if (tsconf.enable == true) {
            str = json_object_get_string(conf_ts_obj, "mode");
            if (str == NULL) {
                MSG("ERROR: fine_timestamp.mode must be configured in %s\n", conf_file);
                return -1;
            } else if (!strncmp(str, "high_capacity", 13) || !strncmp(str, "HIGH_CAPACITY", 13)) {
                tsconf.mode = LGW_FTIME_MODE_HIGH_CAPACITY;
            } else if (!strncmp(str, "all_sf", 6) || !strncmp(str, "ALL_SF", 6)) {
                tsconf.mode = LGW_FTIME_MODE_ALL_SF;
            } else {
                MSG("ERROR: invalid fine timestamp mode: %s (should be high_capacity or all_sf)\n", str);
                return -1;
            }
            MSG("INFO: Configuring precision timestamp with %s mode\n", str);

            /* all parameters parsed, submitting configuration to the HAL */ //Configure the fine timestamp
            if (lgw_ftime_setconf(&tsconf) != LGW_HAL_SUCCESS) {
                MSG("ERROR: Failed to configure fine timestamp\n");
                return -1;
            }
        } else {
            MSG("INFO: Configuring legacy timestamp\n");
        }
    }

    /* set SX1261 configuration */
    memset(&sx1261conf, 0, sizeof sx1261conf); /* initialize configuration structure */
    conf_sx1261_obj = json_object_get_object(conf_obj, "sx1261_conf"); /* fetch value (if possible) */
    if (conf_sx1261_obj == NULL) { //没有sx1261
        MSG("INFO: no configuration for SX1261\n");
    } else {
        /* Global SX1261 configuration */
        str = json_object_get_string(conf_sx1261_obj, "spi_path");
        if (str != NULL) {
            strncpy(sx1261conf.spi_path, str, sizeof sx1261conf.spi_path);
            sx1261conf.spi_path[sizeof sx1261conf.spi_path - 1] = '\0'; /* ensure string termination */
        } else {
            MSG("INFO: SX1261 spi_path is not configured in %s\n", conf_file);
        }
        val = json_object_get_value(conf_sx1261_obj, "rssi_offset"); /* fetch value (if possible) */
        if (json_value_get_type(val) == JSONNumber) {
            sx1261conf.rssi_offset = (int8_t)json_value_get_number(val);
        } else {
            MSG("WARNING: Data type for sx1261_conf.rssi_offset seems wrong, please check\n");
            sx1261conf.rssi_offset = 0;
        }

        /* Spectral Scan configuration */ //频谱扫描必须要有sx1261
        conf_scan_obj = json_object_get_object(conf_sx1261_obj, "spectral_scan"); /* fetch value (if possible) */
        if (conf_scan_obj == NULL) {
            MSG("INFO: no configuration for Spectral Scan\n");
        } else {
            val = json_object_get_value(conf_scan_obj, "enable"); /* fetch value (if possible) */
            if (json_value_get_type(val) == JSONBoolean) {
                /* Enable background spectral scan thread in packet forwarder */
                spectral_scan_params.enable = (bool)json_value_get_boolean(val);
            } else {
                MSG("WARNING: Data type for spectral_scan.enable seems wrong, please check\n");
            }
            if (spectral_scan_params.enable == true) {
                /* Enable the sx1261 radio hardware configuration to allow spectral scan */
                sx1261conf.enable = true;
                MSG("INFO: Spectral Scan with SX1261 is enabled\n");

                /* Get Spectral Scan Parameters */
                val = json_object_get_value(conf_scan_obj, "freq_start"); /* fetch value (if possible) */
                if (json_value_get_type(val) == JSONNumber) {
                    spectral_scan_params.freq_hz_start = (uint32_t)json_value_get_number(val);
                } else {
                    MSG("WARNING: Data type for spectral_scan.freq_start seems wrong, please check\n");
                }
                val = json_object_get_value(conf_scan_obj, "nb_chan"); /* fetch value (if possible) */
                if (json_value_get_type(val) == JSONNumber) {
                    spectral_scan_params.nb_chan = (uint8_t)json_value_get_number(val);
                } else {
                    MSG("WARNING: Data type for spectral_scan.nb_chan seems wrong, please check\n");
                }
                val = json_object_get_value(conf_scan_obj, "nb_scan"); /* fetch value (if possible) */
                if (json_value_get_type(val) == JSONNumber) {
                    spectral_scan_params.nb_scan = (uint16_t)json_value_get_number(val);
                } else {
                    MSG("WARNING: Data type for spectral_scan.nb_scan seems wrong, please check\n");
                }
                val = json_object_get_value(conf_scan_obj, "pace_s"); /* fetch value (if possible) */
                if (json_value_get_type(val) == JSONNumber) {
                    spectral_scan_params.pace_s = (uint32_t)json_value_get_number(val);
                } else {
                    MSG("WARNING: Data type for spectral_scan.pace_s seems wrong, please check\n");
                }
            }
        }

        /* LBT configuration */ //Listen-Before-Talk必须要有sx1261
        conf_lbt_obj = json_object_get_object(conf_sx1261_obj, "lbt"); /* fetch value (if possible) */
        if (conf_lbt_obj == NULL) {
            MSG("INFO: no configuration for LBT\n");
        } else {
            val = json_object_get_value(conf_lbt_obj, "enable"); /* fetch value (if possible) */
            if (json_value_get_type(val) == JSONBoolean) {
                sx1261conf.lbt_conf.enable = (bool)json_value_get_boolean(val);
            } else {
                MSG("WARNING: Data type for lbt.enable seems wrong, please check\n");
            }
            if (sx1261conf.lbt_conf.enable == true) {
                /* Enable the sx1261 radio hardware configuration to allow spectral scan */
                sx1261conf.enable = true;
                MSG("INFO: Listen-Before-Talk with SX1261 is enabled\n");

                val = json_object_get_value(conf_lbt_obj, "rssi_target"); /* fetch value (if possible) */
                if (json_value_get_type(val) == JSONNumber) {
                    sx1261conf.lbt_conf.rssi_target = (int8_t)json_value_get_number(val);
                } else {
                    MSG("WARNING: Data type for lbt.rssi_target seems wrong, please check\n");
                    sx1261conf.lbt_conf.rssi_target = 0;
                }
                /* set LBT channels configuration */
                conf_lbtchan_array = json_object_get_array(conf_lbt_obj, "channels");
                if (conf_lbtchan_array != NULL) {
                    sx1261conf.lbt_conf.nb_channel = json_array_get_count(conf_lbtchan_array);
                    MSG("INFO: %u LBT channels configured\n", sx1261conf.lbt_conf.nb_channel);
                }
                for (i = 0; i < (int)sx1261conf.lbt_conf.nb_channel; i++) {
                    /* Sanity check */
                    if (i >= LGW_LBT_CHANNEL_NB_MAX) {
                        MSG("ERROR: LBT channel %d not supported, skip it\n", i);
                        break;
                    }
                    /* Get LBT channel configuration object from array */
                    conf_lbtchan_obj = json_array_get_object(conf_lbtchan_array, i);

                    /* Channel frequency */
                    val = json_object_dotget_value(conf_lbtchan_obj, "freq_hz"); /* fetch value (if possible) */
                    if (val != NULL) {
                        if (json_value_get_type(val) == JSONNumber) {
                            sx1261conf.lbt_conf.channels[i].freq_hz = (uint32_t)json_value_get_number(val);
                        } else {
                            MSG("WARNING: Data type for lbt.channels[%d].freq_hz seems wrong, please check\n", i);
                            sx1261conf.lbt_conf.channels[i].freq_hz = 0;
                        }
                    } else {
                        MSG("ERROR: no frequency defined for LBT channel %d\n", i);
                        return -1;
                    }

                    /* Channel bandiwdth */
                    val = json_object_dotget_value(conf_lbtchan_obj, "bandwidth"); /* fetch value (if possible) */
                    if (val != NULL) {
                        if (json_value_get_type(val) == JSONNumber) {
                            bw = (uint32_t)json_value_get_number(val);
                            switch(bw) {
                                case 500000: sx1261conf.lbt_conf.channels[i].bandwidth = BW_500KHZ; break;
                                case 250000: sx1261conf.lbt_conf.channels[i].bandwidth = BW_250KHZ; break;
                                case 125000: sx1261conf.lbt_conf.channels[i].bandwidth = BW_125KHZ; break;
                                default: sx1261conf.lbt_conf.channels[i].bandwidth = BW_UNDEFINED;
                            }
                        } else {
                            MSG("WARNING: Data type for lbt.channels[%d].freq_hz seems wrong, please check\n", i);
                            sx1261conf.lbt_conf.channels[i].bandwidth = BW_UNDEFINED;
                        }
                    } else {
                        MSG("ERROR: no bandiwdth defined for LBT channel %d\n", i);
                        return -1;
                    }

                    /* Channel scan time */
                    val = json_object_dotget_value(conf_lbtchan_obj, "scan_time_us"); /* fetch value (if possible) */
                    if (val != NULL) {
                        if (json_value_get_type(val) == JSONNumber) {
                            if ((uint16_t)json_value_get_number(val) == 128) {
                                sx1261conf.lbt_conf.channels[i].scan_time_us = LGW_LBT_SCAN_TIME_128_US;
                            } else if ((uint16_t)json_value_get_number(val) == 5000) {
                                sx1261conf.lbt_conf.channels[i].scan_time_us = LGW_LBT_SCAN_TIME_5000_US;
                            } else {
                                MSG("ERROR: scan time not supported for LBT channel %d, must be 128 or 5000\n", i);
                                return -1;
                            }
                        } else {
                            MSG("WARNING: Data type for lbt.channels[%d].scan_time_us seems wrong, please check\n", i);
                            sx1261conf.lbt_conf.channels[i].scan_time_us = 0;
                        }
                    } else {
                        MSG("ERROR: no scan_time_us defined for LBT channel %d\n", i);
                        return -1;
                    }

                    /* Channel transmit time */
                    val = json_object_dotget_value(conf_lbtchan_obj, "transmit_time_ms"); /* fetch value (if possible) */
                    if (val != NULL) {
                        if (json_value_get_type(val) == JSONNumber) {
                            sx1261conf.lbt_conf.channels[i].transmit_time_ms = (uint16_t)json_value_get_number(val);
                        } else {
                            MSG("WARNING: Data type for lbt.channels[%d].transmit_time_ms seems wrong, please check\n", i);
                            sx1261conf.lbt_conf.channels[i].transmit_time_ms = 0;
                        }
                    } else {
                        MSG("ERROR: no transmit_time_ms defined for LBT channel %d\n", i);
                        return -1;
                    }
                }
            }
        }

        /* all parameters parsed, submitting configuration to the HAL */
        if (lgw_sx1261_setconf(&sx1261conf) != LGW_HAL_SUCCESS) {
            MSG("ERROR: Failed to configure the SX1261 radio\n");
            return -1;
        }
    }

    /* set configuration for RF chains */
    for (i = 0; i < LGW_RF_CHAIN_NB; ++i) { //因为number of RF chains = 2，所以从radio_0依次解析到radio_1
        memset(&rfconf, 0, sizeof rfconf); /* initialize configuration structure */ //rfconf指代SX130x_conf.radio_%i对象
        snprintf(param_name, sizeof param_name, "radio_%i", i); /* compose parameter path inside JSON structure */ //param_name作为中间变量
        val = json_object_get_value(conf_obj, param_name); /* fetch value (if possible) */ //判断json文件中是否有SX130x_conf.radio_0、SX130x_conf.radio_1...等对象
        if (json_value_get_type(val) != JSONObject) {
            MSG("INFO: no configuration for radio %i\n", i);
            continue;
        }
        /* there is an object to configure that radio, let's parse it */
        snprintf(param_name, sizeof param_name, "radio_%i.enable", i);
        val = json_object_dotget_value(conf_obj, param_name);  //rfconf.enable，判断SX130x_conf.radio_%i是否启用
        if (json_value_get_type(val) == JSONBoolean) {
            rfconf.enable = (bool)json_value_get_boolean(val);
        } else {
            rfconf.enable = false;
        }
        if (rfconf.enable == false) { /* radio disabled, nothing else to parse */
            MSG("INFO: radio %i disabled\n", i);
        } else  { /* radio enabled, will parse the other parameters */
            snprintf(param_name, sizeof param_name, "radio_%i.freq", i); //param_name作为中间变量代替radio_%i.freq
            rfconf.freq_hz = (uint32_t)json_object_dotget_number(conf_obj, param_name); //rfconf.freq_hz
            snprintf(param_name, sizeof param_name, "radio_%i.rssi_offset", i); //param_name中作为中间变量代替radio_%i.rssi_offset
            rfconf.rssi_offset = (float)json_object_dotget_number(conf_obj, param_name); //rfconf.rssi_offset
            snprintf(param_name, sizeof param_name, "radio_%i.rssi_tcomp.coeff_a", i); //同上
            rfconf.rssi_tcomp.coeff_a = (float)json_object_dotget_number(conf_obj, param_name);
            snprintf(param_name, sizeof param_name, "radio_%i.rssi_tcomp.coeff_b", i);
            rfconf.rssi_tcomp.coeff_b = (float)json_object_dotget_number(conf_obj, param_name);
            snprintf(param_name, sizeof param_name, "radio_%i.rssi_tcomp.coeff_c", i);
            rfconf.rssi_tcomp.coeff_c = (float)json_object_dotget_number(conf_obj, param_name);
            snprintf(param_name, sizeof param_name, "radio_%i.rssi_tcomp.coeff_d", i);
            rfconf.rssi_tcomp.coeff_d = (float)json_object_dotget_number(conf_obj, param_name);
            snprintf(param_name, sizeof param_name, "radio_%i.rssi_tcomp.coeff_e", i);
            rfconf.rssi_tcomp.coeff_e = (float)json_object_dotget_number(conf_obj, param_name);
            snprintf(param_name, sizeof param_name, "radio_%i.type", i);
            str = json_object_dotget_string(conf_obj, param_name);
            if (!strncmp(str, "SX1255", 6)) { //radio_%i.type = SX1255
                rfconf.type = LGW_RADIO_TYPE_SX1255;
            } else if (!strncmp(str, "SX1257", 6)) { //radio_%i.type = SX1257
                rfconf.type = LGW_RADIO_TYPE_SX1257; 
            } else if (!strncmp(str, "SX1250", 6)) { //radio_%i.type = SX1250
                rfconf.type = LGW_RADIO_TYPE_SX1250;
            } else {
                MSG("WARNING: invalid radio type: %s (should be SX1255 or SX1257 or SX1250)\n", str);
            }
            snprintf(param_name, sizeof param_name, "radio_%i.single_input_mode", i);
            val = json_object_dotget_value(conf_obj, param_name); //rfconf.single_input_mode
            if (json_value_get_type(val) == JSONBoolean) {
                rfconf.single_input_mode = (bool)json_value_get_boolean(val);
            } else {
                rfconf.single_input_mode = false;
            }

            snprintf(param_name, sizeof param_name, "radio_%i.tx_enable", i); //param_name中作为中间变量代替radio_%i.tx_enable
            val = json_object_dotget_value(conf_obj, param_name); //rfconf.tx_enable，判断SX130x_conf.radio_%i.tx_enable是否启用
            if (json_value_get_type(val) == JSONBoolean) {
                rfconf.tx_enable = (bool)json_value_get_boolean(val);
                tx_enable[i] = rfconf.tx_enable; /* update global context for later check */
                if (rfconf.tx_enable == true) { //如果rfchaini可以tx发射
                    /* tx is enabled on this rf chain, we need its frequency range */
                    snprintf(param_name, sizeof param_name, "radio_%i.tx_freq_min", i); //tx_freq_min[i]
                    tx_freq_min[i] = (uint32_t)json_object_dotget_number(conf_obj, param_name);
                    snprintf(param_name, sizeof param_name, "radio_%i.tx_freq_max", i); //tx_freq_max[i]
                    tx_freq_max[i] = (uint32_t)json_object_dotget_number(conf_obj, param_name);
                    if ((tx_freq_min[i] == 0) || (tx_freq_max[i] == 0)) {
                        MSG("WARNING: no frequency range specified for TX rf chain %d\n", i);
                    }

                    /* set configuration for tx gains */
                    memset(&txlut[i], 0, sizeof txlut[i]); /* initialize configuration structure */ //txlut[i]代指SX130x_conf.radio_%i.tx_gain_lut对象
                    snprintf(param_name, sizeof param_name, "radio_%i.tx_gain_lut", i);
                    conf_txlut_array = json_object_dotget_array(conf_obj, param_name);
                    if (conf_txlut_array != NULL) {
                        txlut[i].size = json_array_get_count(conf_txlut_array);
                        /* Detect if we have a sx125x or sx1250 configuration */
                        conf_txgain_obj = json_array_get_object(conf_txlut_array, 0); //conf_txgain_obj即SX130x_conf.radio_%i.tx_gain_lut
                        val = json_object_dotget_value(conf_txgain_obj, "pwr_idx");
                        if (val != NULL) { //有SX130x_conf.radio_%i.tx_gain_lut.pwr_idx的是SX1250
                            printf("INFO: Configuring Tx Gain LUT for rf_chain %u with %u indexes for sx1250\n", i, txlut[i].size);
                            sx1250_tx_lut = true;
                        } else { //没有SX130x_conf.radio_%i.tx_gain_lut.pwr_idx的是SX125x
                            printf("INFO: Configuring Tx Gain LUT for rf_chain %u with %u indexes for sx125x\n", i, txlut[i].size);
                            sx1250_tx_lut = false;
                        }
                        /* Parse the table */
                        for (j = 0; j < (int)txlut[i].size; j++) {
                             /* Sanity check */
                            if (j >= TX_GAIN_LUT_SIZE_MAX) {
                                printf("ERROR: TX Gain LUT [%u] index %d not supported, skip it\n", i, j);
                                break;
                            }
                            /* Get TX gain object from LUT */
                            conf_txgain_obj = json_array_get_object(conf_txlut_array, j);
                            /* rf power */
                            val = json_object_dotget_value(conf_txgain_obj, "rf_power"); //txlut[i].lut[j].rf_power代指SX130x_conf.radio_%i.tx_gain_lut第j条内容.rf_power
                            if (json_value_get_type(val) == JSONNumber) {
                                txlut[i].lut[j].rf_power = (int8_t)json_value_get_number(val);
                            } else {
                                printf("WARNING: Data type for %s[%d] seems wrong, please check\n", "rf_power", j);
                                txlut[i].lut[j].rf_power = 0;
                            }
                            /* PA gain */
                            val = json_object_dotget_value(conf_txgain_obj, "pa_gain"); //txlut[i].lut[j].pa_gain
                            if (json_value_get_type(val) == JSONNumber) {
                                txlut[i].lut[j].pa_gain = (uint8_t)json_value_get_number(val);
                            } else {
                                printf("WARNING: Data type for %s[%d] seems wrong, please check\n", "pa_gain", j);
                                txlut[i].lut[j].pa_gain = 0;
                            }
                            if (sx1250_tx_lut == false) { //非sx125x
                                /* DIG gain */
                                val = json_object_dotget_value(conf_txgain_obj, "dig_gain"); //txlut[i].lut[j].dig_gain
                                if (json_value_get_type(val) == JSONNumber) {
                                    txlut[i].lut[j].dig_gain = (uint8_t)json_value_get_number(val);
                                } else {
                                    printf("WARNING: Data type for %s[%d] seems wrong, please check\n", "dig_gain", j);
                                    txlut[i].lut[j].dig_gain = 0;
                                }
                                /* DAC gain */
                                val = json_object_dotget_value(conf_txgain_obj, "dac_gain"); //txlut[i].lut[j].dac_gain
                                if (json_value_get_type(val) == JSONNumber) {
                                    txlut[i].lut[j].dac_gain = (uint8_t)json_value_get_number(val);
                                } else {
                                    printf("WARNING: Data type for %s[%d] seems wrong, please check\n", "dac_gain", j);
                                    txlut[i].lut[j].dac_gain = 3; /* This is the only dac_gain supported for now */
                                }
                                /* MIX gain */
                                val = json_object_dotget_value(conf_txgain_obj, "mix_gain"); //txlut[i].lut[j].mix_gain
                                if (json_value_get_type(val) == JSONNumber) {
                                    txlut[i].lut[j].mix_gain = (uint8_t)json_value_get_number(val);
                                } else {
                                    printf("WARNING: Data type for %s[%d] seems wrong, please check\n", "mix_gain", j);
                                    txlut[i].lut[j].mix_gain = 0;
                                }
                            } else { //sx1250
                                /* TODO: rework this, should not be needed for sx1250 */
                                txlut[i].lut[j].mix_gain = 5;

                                /* power index */
                                val = json_object_dotget_value(conf_txgain_obj, "pwr_idx"); //txlut[i].lut[j].pwr_idx
                                if (json_value_get_type(val) == JSONNumber) {
                                    txlut[i].lut[j].pwr_idx = (uint8_t)json_value_get_number(val);
                                } else {
                                    printf("WARNING: Data type for %s[%d] seems wrong, please check\n", "pwr_idx", j);
                                    txlut[i].lut[j].pwr_idx = 0;
                                }
                            }
                        }
                        /* all parameters parsed, submitting configuration to the HAL */
                        if (txlut[i].size > 0) {
                            if (lgw_txgain_setconf(i, &txlut[i]) != LGW_HAL_SUCCESS) { //to set the configuration of the concentrator gain table
                                MSG("ERROR: Failed to configure concentrator TX Gain LUT for rf_chain %u\n", i);
                                return -1;
                            }
                        } else {
                            MSG("WARNING: No TX gain LUT defined for rf_chain %u\n", i);
                        }
                    } else {
                        MSG("WARNING: No TX gain LUT defined for rf_chain %u\n", i);
                    }
                }
            } else { 
                rfconf.tx_enable = false; //radio_i没启用
            }
            MSG("INFO: radio %i enabled (type %s), center frequency %u, RSSI offset %f, tx enabled %d, single input mode %d\n", i, str, rfconf.freq_hz, rfconf.rssi_offset, rfconf.tx_enable, rfconf.single_input_mode);
        }
        /* all parameters parsed, submitting configuration to the HAL */
        if (lgw_rxrf_setconf(i, &rfconf) != LGW_HAL_SUCCESS) { //to set the configuration of the radio channels
            MSG("ERROR: invalid configuration for radio %i\n", i);
            return -1;
        }
    }

    /* set configuration for demodulators */
    memset(&demodconf, 0, sizeof demodconf); /* initialize configuration structure */
    val = json_object_get_value(conf_obj, "chan_multiSF_All"); /* fetch value (if possible) */ //conf_obj为获取到的大括号里的内容
    if (json_value_get_type(val) != JSONObject) { //变量类型不对
        MSG("INFO: no configuration for LoRa multi-SF spreading factors enabling\n");
    } else { //变量类型正确
        conf_demod_array = json_object_dotget_array(conf_obj, "chan_multiSF_All.spreading_factor_enable"); //获取spreading_factor_enable里的中括号数组
        if ((conf_demod_array != NULL) && ((size = json_array_get_count(conf_demod_array)) <= LGW_MULTI_NB)) {
            for (i = 0; i < (int)size; i++) {
                number = json_array_get_number(conf_demod_array, i);
                if (number < 5 || number > 12) { //数组内数字不在5到12之间
                    MSG("WARNING: failed to parse chan_multiSF_All.spreading_factor_enable (wrong value at idx %d)\n", i);
                    demodconf.multisf_datarate = 0xFF; /* enable all SFs */
                    break;
                } else { //数组内数字在5到12之间
                    /* set corresponding bit in the bitmask SF5 is LSB -> SF12 is MSB */
                    demodconf.multisf_datarate |= (1 << (number - 5));
                }
            }
        } else { //中括号数组内数字个数小于0或者大于8
            MSG("WARNING: failed to parse chan_multiSF_All.spreading_factor_enable\n");
            demodconf.multisf_datarate = 0xFF; /* enable all SFs */ //所有位掩码都为1
        }
          /* all parameters parsed, submitting configuration to the HAL */
        if (lgw_demod_setconf(&demodconf) != LGW_HAL_SUCCESS) {
            MSG("ERROR: invalid configuration for demodulation parameters\n");
            return -1;
        }
    }

    /* set configuration for Lora multi-SF channels (bandwidth cannot be set) */
    for (i = 0; i < LGW_MULTI_NB; ++i) { //最多支持8条
        memset(&ifconf, 0, sizeof ifconf); /* initialize configuration structure */ //ifconf指代SX130x_conf.chan_multiSF_i对象
        snprintf(param_name, sizeof param_name, "chan_multiSF_%i", i); /* compose parameter path inside JSON structure */
        val = json_object_get_value(conf_obj, param_name); /* fetch value (if possible) */
        if (json_value_get_type(val) != JSONObject) {
            MSG("INFO: no configuration for Lora multi-SF channel %i\n", i);
            continue;
        }
        /* there is an object to configure that Lora multi-SF channel, let's parse it */
        snprintf(param_name, sizeof param_name, "chan_multiSF_%i.enable", i);
        val = json_object_dotget_value(conf_obj, param_name);  //ifconf.enable，判断SX130x_conf.chan_multiSF_%i是否启用
        if (json_value_get_type(val) == JSONBoolean) {
            ifconf.enable = (bool)json_value_get_boolean(val);
        } else {
            ifconf.enable = false;
        }
        if (ifconf.enable == false) { /* Lora multi-SF channel disabled, nothing else to parse */
            MSG("INFO: Lora multi-SF channel %i disabled\n", i);
        } else  { /* Lora multi-SF channel enabled, will parse the other parameters */
            snprintf(param_name, sizeof param_name, "chan_multiSF_%i.radio", i); //ifconf.rf_chain
            ifconf.rf_chain = (uint32_t)json_object_dotget_number(conf_obj, param_name);
            snprintf(param_name, sizeof param_name, "chan_multiSF_%i.if", i); //ifconf.freq_hz
            ifconf.freq_hz = (int32_t)json_object_dotget_number(conf_obj, param_name);
            // TODO: handle individual SF enabling and disabling (spread_factor)
            MSG("INFO: Lora multi-SF channel %i>  radio %i, IF %i Hz, 125 kHz bw, SF 5 to 12\n", i, ifconf.rf_chain, ifconf.freq_hz);
        }
        /* all parameters parsed, submitting configuration to the HAL */
        if (lgw_rxif_setconf(i, &ifconf) != LGW_HAL_SUCCESS) { //to set the configuration of the 0-7 IF+modem channels
            MSG("ERROR: invalid configuration for Lora multi-SF channel %i\n", i);
            return -1;
        }
    }

    /* set configuration for Lora standard channel */
    memset(&ifconf, 0, sizeof ifconf); /* initialize configuration structure */
    val = json_object_get_value(conf_obj, "chan_Lora_std"); /* fetch value (if possible) */
    if (json_value_get_type(val) != JSONObject) {
        MSG("INFO: no configuration for Lora standard channel\n");
    } else {
        val = json_object_dotget_value(conf_obj, "chan_Lora_std.enable"); //ifconf.enable，判断SX130x_conf.chan_Lora_std是否启用
        if (json_value_get_type(val) == JSONBoolean) {
            ifconf.enable = (bool)json_value_get_boolean(val);
        } else {
            ifconf.enable = false;
        }
        if (ifconf.enable == false) {
            MSG("INFO: Lora standard channel %i disabled\n", i);
        } else  {
            ifconf.rf_chain = (uint32_t)json_object_dotget_number(conf_obj, "chan_Lora_std.radio"); //ifconf.rf_chain
            ifconf.freq_hz = (int32_t)json_object_dotget_number(conf_obj, "chan_Lora_std.if"); //ifconf.freq_hz
            bw = (uint32_t)json_object_dotget_number(conf_obj, "chan_Lora_std.bandwidth"); //bw是中间变量
            switch(bw) { //ifconf.bandwidth
                case 500000: ifconf.bandwidth = BW_500KHZ; break;
                case 250000: ifconf.bandwidth = BW_250KHZ; break;
                case 125000: ifconf.bandwidth = BW_125KHZ; break;
                default: ifconf.bandwidth = BW_UNDEFINED;
            }
            sf = (uint32_t)json_object_dotget_number(conf_obj, "chan_Lora_std.spread_factor"); //sf是中间变量
            switch(sf) { //ifconf.datarate
                case  5: ifconf.datarate = DR_LORA_SF5;  break;
                case  6: ifconf.datarate = DR_LORA_SF6;  break;
                case  7: ifconf.datarate = DR_LORA_SF7;  break;
                case  8: ifconf.datarate = DR_LORA_SF8;  break;
                case  9: ifconf.datarate = DR_LORA_SF9;  break;
                case 10: ifconf.datarate = DR_LORA_SF10; break;
                case 11: ifconf.datarate = DR_LORA_SF11; break;
                case 12: ifconf.datarate = DR_LORA_SF12; break;
                default: ifconf.datarate = DR_UNDEFINED;
            }
            val = json_object_dotget_value(conf_obj, "chan_Lora_std.implicit_hdr");
            if (json_value_get_type(val) == JSONBoolean) {
                ifconf.implicit_hdr = (bool)json_value_get_boolean(val);
            } else {
                ifconf.implicit_hdr = false;
            }
            if (ifconf.implicit_hdr == true) { //如果是隐式报头
                val = json_object_dotget_value(conf_obj, "chan_Lora_std.implicit_payload_length"); //ifconf.implicit_payload_length必须的
                if (json_value_get_type(val) == JSONNumber) {
                    ifconf.implicit_payload_length = (uint8_t)json_value_get_number(val);
                } else {
                    MSG("ERROR: payload length setting is mandatory for implicit header mode\n");
                    return -1;
                }
                val = json_object_dotget_value(conf_obj, "chan_Lora_std.implicit_crc_en"); //ifconf.implicit_crc_en必须的
                if (json_value_get_type(val) == JSONBoolean) {
                    ifconf.implicit_crc_en = (bool)json_value_get_boolean(val);
                } else {
                    MSG("ERROR: CRC enable setting is mandatory for implicit header mode\n");
                    return -1;
                }
                val = json_object_dotget_value(conf_obj, "chan_Lora_std.implicit_coderate"); //ifconf.implicit_coderate必须的
                if (json_value_get_type(val) == JSONNumber) {
                    ifconf.implicit_coderate = (uint8_t)json_value_get_number(val);
                } else {
                    MSG("ERROR: coding rate setting is mandatory for implicit header mode\n");
                    return -1;
                }
            }

            MSG("INFO: Lora std channel> radio %i, IF %i Hz, %u Hz bw, SF %u, %s\n", ifconf.rf_chain, ifconf.freq_hz, bw, sf, (ifconf.implicit_hdr == true) ? "Implicit header" : "Explicit header");
        }
        if (lgw_rxif_setconf(8, &ifconf) != LGW_HAL_SUCCESS) { //to set the configuration of the 8th IF+modem channels
            MSG("ERROR: invalid configuration for Lora standard channel\n");
            return -1;
        }
    }

    /* set configuration for FSK channel */
    memset(&ifconf, 0, sizeof ifconf); /* initialize configuration structure */ //ifconf指代SX130x_conf.chan_FSK对象
    val = json_object_get_value(conf_obj, "chan_FSK"); /* fetch value (if possible) */
    if (json_value_get_type(val) != JSONObject) {
        MSG("INFO: no configuration for FSK channel\n");
    } else {
        val = json_object_dotget_value(conf_obj, "chan_FSK.enable"); //ifconf.enable，判断SX130x_conf.chan_FSK是否启用
        if (json_value_get_type(val) == JSONBoolean) {
            ifconf.enable = (bool)json_value_get_boolean(val);
        } else {
            ifconf.enable = false;
        }
        if (ifconf.enable == false) {
            MSG("INFO: FSK channel %i disabled\n", i);
        } else  {
            ifconf.rf_chain = (uint32_t)json_object_dotget_number(conf_obj, "chan_FSK.radio"); //ifconf.rf_chain
            ifconf.freq_hz = (int32_t)json_object_dotget_number(conf_obj, "chan_FSK.if"); //ifconf.freq_hz
            bw = (uint32_t)json_object_dotget_number(conf_obj, "chan_FSK.bandwidth");  //bw是中间变量，SX130x_conf.chan_FSK.freq_deviation在模板里没有
            fdev = (uint32_t)json_object_dotget_number(conf_obj, "chan_FSK.freq_deviation"); //fdev是中间变量
            ifconf.datarate = (uint32_t)json_object_dotget_number(conf_obj, "chan_FSK.datarate"); //ifconf.datarate

            /* if chan_FSK.bandwidth is set, it has priority over chan_FSK.freq_deviation */
            if ((bw == 0) && (fdev != 0)) {
                bw = 2 * fdev + ifconf.datarate;
            }
            if      (bw == 0)      ifconf.bandwidth = BW_UNDEFINED;
#if 0 /* TODO */
            else if (bw <= 7800)   ifconf.bandwidth = BW_7K8HZ;
            else if (bw <= 15600)  ifconf.bandwidth = BW_15K6HZ;
            else if (bw <= 31200)  ifconf.bandwidth = BW_31K2HZ;
            else if (bw <= 62500)  ifconf.bandwidth = BW_62K5HZ;
#endif
            else if (bw <= 125000) ifconf.bandwidth = BW_125KHZ;
            else if (bw <= 250000) ifconf.bandwidth = BW_250KHZ;
            else if (bw <= 500000) ifconf.bandwidth = BW_500KHZ;
            else ifconf.bandwidth = BW_UNDEFINED;

            MSG("INFO: FSK channel> radio %i, IF %i Hz, %u Hz bw, %u bps datarate\n", ifconf.rf_chain, ifconf.freq_hz, bw, ifconf.datarate);
        }
        if (lgw_rxif_setconf(9, &ifconf) != LGW_HAL_SUCCESS) { //to set the configuration of the 9th IF+modem channels
            MSG("ERROR: invalid configuration for FSK channel\n");
            return -1;
        }
    }
    json_value_free(root_val);

    return 0;
}

static int parse_gateway_configuration(const char * conf_file) {
    const char conf_obj_name[] = "gateway_conf";
    JSON_Value *root_val;
    JSON_Object *conf_obj = NULL;
    JSON_Value *val = NULL; /* needed to detect the absence of some fields */
    const char *str; /* pointer to sub-strings in the JSON data */
    unsigned long long ull = 0; //存储MAC地址的中间变量

    /* try to parse JSON */ //判断是否是JSON文件
    root_val = json_parse_file_with_comments(conf_file);
    if (root_val == NULL) {
        MSG("ERROR: %s is not a valid JSON file\n", conf_file);
        exit(EXIT_FAILURE);
    }

    /* point to the gateway configuration object */ //判断json文件中是否有gateway_conf对象
    conf_obj = json_object_get_object(json_value_get_object(root_val), conf_obj_name);
    if (conf_obj == NULL) {
        MSG("INFO: %s does not contain a JSON object named %s\n", conf_file, conf_obj_name);
        return -1;
    } else {
        MSG("INFO: %s does contain a JSON object named %s, parsing gateway parameters\n", conf_file, conf_obj_name);
    }

    /* gateway unique identifier (aka MAC address) (optional) */
    str = json_object_get_string(conf_obj, "gateway_ID");
    if (str != NULL) {
        sscanf(str, "%llx", &ull); //64位16进制整数
        lgwm = ull;
        MSG("INFO: gateway MAC address is configured to %016llX\n", ull);
    }

    /* server hostname or IP address (optional) */
    str = json_object_get_string(conf_obj, "server_address"); //serv_addr
    if (str != NULL) {
        strncpy(serv_addr, str, sizeof serv_addr);
        serv_addr[sizeof serv_addr - 1] = '\0'; /* ensure string termination */
        MSG("INFO: server hostname or IP address is configured to \"%s\"\n", serv_addr);
    }

    /* get up and down ports (optional) */
    val = json_object_get_value(conf_obj, "serv_port_up"); //serv_port_up
    if (val != NULL) {
        snprintf(serv_port_up, sizeof serv_port_up, "%u", (uint16_t)json_value_get_number(val));
        MSG("INFO: upstream port is configured to \"%s\"\n", serv_port_up);
    }
    val = json_object_get_value(conf_obj, "serv_port_down"); //serv_port_down
    if (val != NULL) {
        snprintf(serv_port_down, sizeof serv_port_down, "%u", (uint16_t)json_value_get_number(val));
        MSG("INFO: downstream port is configured to \"%s\"\n", serv_port_down);
    }

    /* get keep-alive interval (in seconds) for downstream (optional) */
    val = json_object_get_value(conf_obj, "keepalive_interval"); //keepalive_time
    if (val != NULL) {
        keepalive_time = (int)json_value_get_number(val);
        MSG("INFO: downstream keep-alive interval is configured to %u seconds\n", keepalive_time);
    }

    /* get interval (in seconds) for statistics display (optional) */
    val = json_object_get_value(conf_obj, "stat_interval"); //stat_interval
    if (val != NULL) {
        stat_interval = (unsigned)json_value_get_number(val);
        MSG("INFO: statistics display interval is configured to %u seconds\n", stat_interval);
    }

    /* get time-out value (in ms) for upstream datagrams (optional) */
    val = json_object_get_value(conf_obj, "push_timeout_ms"); //push_timeout_half.tv_usec/500
    if (val != NULL) {
        push_timeout_half.tv_usec = 500 * (long int)json_value_get_number(val);
        MSG("INFO: upstream PUSH_DATA time-out is configured to %u ms\n", (unsigned)(push_timeout_half.tv_usec / 500));
    }

    /* packet filtering parameters */
    val = json_object_get_value(conf_obj, "forward_crc_valid"); //fwd_valid_pkt
    if (json_value_get_type(val) == JSONBoolean) {
        fwd_valid_pkt = (bool)json_value_get_boolean(val);
    }
    MSG("INFO: packets received with a valid CRC will%s be forwarded\n", (fwd_valid_pkt ? "" : " NOT"));
    val = json_object_get_value(conf_obj, "forward_crc_error"); //fwd_error_pkt
    if (json_value_get_type(val) == JSONBoolean) {
        fwd_error_pkt = (bool)json_value_get_boolean(val);
    }
    MSG("INFO: packets received with a CRC error will%s be forwarded\n", (fwd_error_pkt ? "" : " NOT"));
    val = json_object_get_value(conf_obj, "forward_crc_disabled"); //fwd_nocrc_pkt
    if (json_value_get_type(val) == JSONBoolean) {
        fwd_nocrc_pkt = (bool)json_value_get_boolean(val);
    }
    MSG("INFO: packets received with no CRC will%s be forwarded\n", (fwd_nocrc_pkt ? "" : " NOT"));

    /* GPS module TTY path (optional) */
    str = json_object_get_string(conf_obj, "gps_tty_path"); //gps_tty_path
    if (str != NULL) {
        strncpy(gps_tty_path, str, sizeof gps_tty_path);
        gps_tty_path[sizeof gps_tty_path - 1] = '\0'; /* ensure string termination */
        MSG("INFO: GPS serial port path is configured to \"%s\"\n", gps_tty_path);
    }

    /* get reference coordinates */
    val = json_object_get_value(conf_obj, "ref_latitude"); //reference_coord.lat
    if (val != NULL) {
        reference_coord.lat = (double)json_value_get_number(val);
        MSG("INFO: Reference latitude is configured to %f deg\n", reference_coord.lat);
    }
    val = json_object_get_value(conf_obj, "ref_longitude"); //reference_coord.lon
    if (val != NULL) {
        reference_coord.lon = (double)json_value_get_number(val);
        MSG("INFO: Reference longitude is configured to %f deg\n", reference_coord.lon);
    }
    val = json_object_get_value(conf_obj, "ref_altitude"); //reference_coord.alt
    if (val != NULL) {
        reference_coord.alt = (short)json_value_get_number(val);
        MSG("INFO: Reference altitude is configured to %i meters\n", reference_coord.alt);
    }

    /* Gateway GPS coordinates hardcoding (aka. faking) option */
    val = json_object_get_value(conf_obj, "fake_gps"); //gps_fake_enable，判断fake_gps是否启用
    if (json_value_get_type(val) == JSONBoolean) {
        gps_fake_enable = (bool)json_value_get_boolean(val);
        if (gps_fake_enable == true) {
            MSG("INFO: fake GPS is enabled\n");
        } else {
            MSG("INFO: fake GPS is disabled\n");
        }
    }

    /* Beacon signal period (optional) */ //下面都是class B beacon发射参数
    val = json_object_get_value(conf_obj, "beacon_period"); //beacon_period 
    if (val != NULL) {
        beacon_period = (uint32_t)json_value_get_number(val);
        if ((beacon_period > 0) && (beacon_period < 6)) {
            MSG("ERROR: invalid configuration for Beacon period, must be >= 6s\n");
            return -1;
        } else {
            MSG("INFO: Beaconing period is configured to %u seconds\n", beacon_period);
        }
    }

    /* Beacon TX frequency (optional) */
    val = json_object_get_value(conf_obj, "beacon_freq_hz"); //beacon_freq_hzs
    if (val != NULL) {
        beacon_freq_hz = (uint32_t)json_value_get_number(val);
        MSG("INFO: Beaconing signal will be emitted at %u Hz\n", beacon_freq_hz);
    }

    /* Number of beacon channels (optional) */
    val = json_object_get_value(conf_obj, "beacon_freq_nb"); //beacon_freq_nb
    if (val != NULL) {
        beacon_freq_nb = (uint8_t)json_value_get_number(val);
        MSG("INFO: Beaconing channel number is set to %u\n", beacon_freq_nb);
    }

    /* Frequency step between beacon channels (optional) */
    val = json_object_get_value(conf_obj, "beacon_freq_step");//beacon_freq_step
    if (val != NULL) {
        beacon_freq_step = (uint32_t)json_value_get_number(val);
        MSG("INFO: Beaconing channel frequency step is set to %uHz\n", beacon_freq_step);
    }

    /* Beacon datarate (optional) */
    val = json_object_get_value(conf_obj, "beacon_datarate"); //beacon_datarate
    if (val != NULL) {
        beacon_datarate = (uint8_t)json_value_get_number(val);
        MSG("INFO: Beaconing datarate is set to SF%d\n", beacon_datarate);
    }

    /* Beacon modulation bandwidth (optional) */
    val = json_object_get_value(conf_obj, "beacon_bw_hz"); //beacon_bw_hz
    if (val != NULL) {
        beacon_bw_hz = (uint32_t)json_value_get_number(val);
        MSG("INFO: Beaconing modulation bandwidth is set to %dHz\n", beacon_bw_hz);
    }

    /* Beacon TX power (optional) */
    val = json_object_get_value(conf_obj, "beacon_power"); //beacon_power
    if (val != NULL) {
        beacon_power = (int8_t)json_value_get_number(val);
        MSG("INFO: Beaconing TX power is set to %ddBm\n", beacon_power);
    }

    /* Beacon information descriptor (optional) */
    val = json_object_get_value(conf_obj, "beacon_infodesc"); //beacon_infodesc
    if (val != NULL) {
        beacon_infodesc = (uint8_t)json_value_get_number(val);
        MSG("INFO: Beaconing information descriptor is set to %u\n", beacon_infodesc);
    }

    /* Auto-quit threshold (optional) */
    val = json_object_get_value(conf_obj, "autoquit_threshold"); //autoquit_threshold
    if (val != NULL) {
        autoquit_threshold = (uint32_t)json_value_get_number(val);
        MSG("INFO: Auto-quit after %u non-acknowledged PULL_DATA\n", autoquit_threshold);
    }

    /* free JSON parsing data structure */
    json_value_free(root_val);
    return 0;
}

static int parse_debug_configuration(const char * conf_file) {
    int i;
    const char conf_obj_name[] = "debug_conf";
    JSON_Value *root_val;
    JSON_Object *conf_obj = NULL;
    JSON_Array *conf_array = NULL;
    JSON_Object *conf_obj_array = NULL;
    const char *str; /* pointer to sub-strings in the JSON data */

    /* Initialize structure */
    memset(&debugconf, 0, sizeof debugconf); //debugconf指代debug_conf对象

    /* try to parse JSON */ //判断是否是JSON文件
    root_val = json_parse_file_with_comments(conf_file);
    if (root_val == NULL) {
        MSG("ERROR: %s is not a valid JSON file\n", conf_file);
        exit(EXIT_FAILURE);
    }

    /* point to the gateway configuration object */ //判断json文件中是否有debug_conf对象
    conf_obj = json_object_get_object(json_value_get_object(root_val), conf_obj_name);
    if (conf_obj == NULL) {
        MSG("INFO: %s does not contain a JSON object named %s\n", conf_file, conf_obj_name);
        json_value_free(root_val);
        return -1;
    } else {
        MSG("INFO: %s does contain a JSON object named %s, parsing debug parameters\n", conf_file, conf_obj_name);
    }

    /* Get reference payload configuration */
    conf_array = json_object_get_array (conf_obj, "ref_payload"); //查看是否有debug_conf.ref_payload对象
    if (conf_array != NULL) {
        debugconf.nb_ref_payload = json_array_get_count(conf_array);
        MSG("INFO: got %u debug reference payload\n", debugconf.nb_ref_payload); //理论上限16条，求出实际有几条ref_payload

        for (i = 0; i < (int)debugconf.nb_ref_payload; i++) { //求出每条实际ref_payload的id
            conf_obj_array = json_array_get_object(conf_array, i);
            /* id */
            str = json_object_get_string(conf_obj_array, "id"); //debugconf.ref_payload[i].id
            if (str != NULL) {
                sscanf(str, "0x%08X", &(debugconf.ref_payload[i].id));
                MSG("INFO: reference payload ID %d is 0x%08X\n", i, debugconf.ref_payload[i].id);
            }

            /* global count */
            nb_pkt_received_ref[i] = 0;
        }
    }

    /* Get log file configuration */
    str = json_object_get_string(conf_obj, "log_file"); //debugconf.log_file_name
    if (str != NULL) {
        strncpy(debugconf.log_file_name, str, sizeof debugconf.log_file_name);
        debugconf.log_file_name[sizeof debugconf.log_file_name - 1] = '\0'; /* ensure string termination */
        MSG("INFO: setting debug log file name to %s\n", debugconf.log_file_name);
    }

    /* Commit configuration */
    if (lgw_debug_setconf(&debugconf) != LGW_HAL_SUCCESS) { //Configure the debug context
        MSG("ERROR: Failed to configure debug\n");
        json_value_free(root_val);
        return -1;
    }

    /* free JSON parsing data structure */
    json_value_free(root_val);
    return 0;
}

static uint16_t crc16(const uint8_t * data, unsigned size) { //对发射的包进行crc检验
    const uint16_t crc_poly = 0x1021;
    const uint16_t init_val = 0x0000;
    uint16_t x = init_val;
    unsigned i, j;

    if (data == NULL)  {
        return 0;
    }

    for (i=0; i<size; ++i) {
        x ^= (uint16_t)data[i] << 8;
        for (j=0; j<8; ++j) {
            x = (x & 0x8000) ? (x<<1) ^ crc_poly : (x<<1);
        }
    }

    return x;
}

static double difftimespec(struct timespec end, struct timespec beginning) { //计算时间差
    double x;

    x = 1E-9 * (double)(end.tv_nsec - beginning.tv_nsec);
    x += (double)(end.tv_sec - beginning.tv_sec);

    return x;
}

static int send_tx_ack(uint8_t token_h, uint8_t token_l, enum jit_error_e error, int32_t error_value) { //send acknoledge datagram to server: TX_ACK packet
    uint8_t buff_ack[ACK_BUFF_SIZE]; /* buffer to give feedback to server */
    int buff_index;
    int j;

    /* reset buffer */
    memset(&buff_ack, 0, sizeof buff_ack);

    /* Prepare downlink feedback to be sent to server */ //TX_ACK packet
    buff_ack[0] = PROTOCOL_VERSION; //protocol version = 2
    buff_ack[1] = token_h; //same token as the PULL_RESP packet to acknowledge
    buff_ack[2] = token_l;
    buff_ack[3] = PKT_TX_ACK; //TX_ACK identifier 0x05
    *(uint32_t *)(buff_ack + 4) = net_mac_h; //Gateway unique identifier (MAC address)
    *(uint32_t *)(buff_ack + 8) = net_mac_l;
    buff_index = 12; /* 12-byte header */

    /* Put no JSON string if there is nothing to report */ //If no JSON is present (empty string), this means than no error occurred
    if (error != JIT_ERROR_OK) { //有错误需要在json汇报
        /* start of JSON structure */ //Downstream JSON data structure
        memcpy((void *)(buff_ack + buff_index), (void *)"{\"txpk_ack\":{", 13); //json object txpk_ack
        buff_index += 13;
        /* set downlink error/warning status in JSON structure */
        switch( error ) {
            case JIT_ERROR_TX_POWER:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"warn\":", 7); //仅JIT_ERROR_TX_POWER为warning
                buff_index += 7;
                break;
            default:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"error\":", 8);
                buff_index += 8;
                break;
        }
        /* set error/warning type in JSON structure */
        switch (error) {
            case JIT_ERROR_FULL:
            case JIT_ERROR_COLLISION_PACKET:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"COLLISION_PACKET\"", 18);
                buff_index += 18;
                /* update stats */
                pthread_mutex_lock(&mx_meas_dw);
                meas_nb_tx_rejected_collision_packet += 1;
                pthread_mutex_unlock(&mx_meas_dw);
                break;
            case JIT_ERROR_TOO_LATE:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"TOO_LATE\"", 10);
                buff_index += 10;
                /* update stats */
                pthread_mutex_lock(&mx_meas_dw);
                meas_nb_tx_rejected_too_late += 1;
                pthread_mutex_unlock(&mx_meas_dw);
                break;
            case JIT_ERROR_TOO_EARLY:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"TOO_EARLY\"", 11);
                buff_index += 11;
                /* update stats */
                pthread_mutex_lock(&mx_meas_dw);
                meas_nb_tx_rejected_too_early += 1;
                pthread_mutex_unlock(&mx_meas_dw);
                break;
            case JIT_ERROR_COLLISION_BEACON:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"COLLISION_BEACON\"", 18);
                buff_index += 18;
                /* update stats */
                pthread_mutex_lock(&mx_meas_dw);
                meas_nb_tx_rejected_collision_beacon += 1;
                pthread_mutex_unlock(&mx_meas_dw);
                break;
            case JIT_ERROR_TX_FREQ:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"TX_FREQ\"", 9);
                buff_index += 9;
                break;
            case JIT_ERROR_TX_POWER: //如果error为JIT_ERROR_TX_POWER
                memcpy((void *)(buff_ack + buff_index), (void *)"\"TX_POWER\"", 10);
                buff_index += 10;
                break;
            case JIT_ERROR_GPS_UNLOCKED:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"GPS_UNLOCKED\"", 14);
                buff_index += 14;
                break;
            default:
                memcpy((void *)(buff_ack + buff_index), (void *)"\"UNKNOWN\"", 9);
                buff_index += 9;
                break;
        }
        /* set error/warning details in JSON structure */
        switch (error) {
            case JIT_ERROR_TX_POWER:
                j = snprintf((char *)(buff_ack + buff_index), ACK_BUFF_SIZE-buff_index, ",\"value\":%d", error_value);
                if (j > 0) {
                    buff_index += j;
                } else {
                    MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                    exit(EXIT_FAILURE);
                }
                break;
            default:
                /* Do nothing */
                break;
        }
        /* end of JSON structure */
        memcpy((void *)(buff_ack + buff_index), (void *)"}}", 2);
        buff_index += 2;
    }

    buff_ack[buff_index] = 0; /* add string terminator, for safety */

    /* send datagram to server */ //That packet type is used by the gateway to send a feedback to the server to inform if a downlink request has been accepted or rejected by the gateway；The datagram may optionnaly contain a JSON string to give more details on acknoledge. If no JSON is present (empty string), this means than no error occured.
    return send(sock_down, (void *)buff_ack, buff_index, 0);
}

/* -------------------------------------------------------------------------- */
/* --- MAIN FUNCTION -------------------------------------------------------- */

int main(int argc, char ** argv)
{
    struct sigaction sigact; /* SIGQUIT&SIGINT&SIGTERM signal handling */
    int i; /* loop variable and temporary variable for return value */
    int x;
    int l, m;

    /* configuration file related */ //配置文件
    const char defaut_conf_fname[] = JSON_CONF_DEFAULT;
    const char * conf_fname = defaut_conf_fname; /* pointer to a string we won't touch */

    /* threads */
    pthread_t thrid_up;
    pthread_t thrid_down;
    pthread_t thrid_gps;
    pthread_t thrid_valid;
    pthread_t thrid_jit;
    pthread_t thrid_ss;

    /* network socket creation */ //socket套接字网络通信
    struct addrinfo hints;
    struct addrinfo *result; /* store result of getaddrinfo */
    struct addrinfo *q; /* pointer to move into *result data */
    char host_name[64];
    char port_name[64];

    /* variables to get local copies of measurements */
    uint32_t cp_nb_rx_rcv;
    uint32_t cp_nb_rx_ok;
    uint32_t cp_nb_rx_bad;
    uint32_t cp_nb_rx_nocrc;
    uint32_t cp_up_pkt_fwd;
    uint32_t cp_up_network_byte;
    uint32_t cp_up_payload_byte;
    uint32_t cp_up_dgram_sent;
    uint32_t cp_up_ack_rcv;
    uint32_t cp_dw_pull_sent;
    uint32_t cp_dw_ack_rcv;
    uint32_t cp_dw_dgram_rcv;
    uint32_t cp_dw_network_byte;
    uint32_t cp_dw_payload_byte;
    uint32_t cp_nb_tx_ok;
    uint32_t cp_nb_tx_fail;
    uint32_t cp_nb_tx_requested = 0;
    uint32_t cp_nb_tx_rejected_collision_packet = 0;
    uint32_t cp_nb_tx_rejected_collision_beacon = 0;
    uint32_t cp_nb_tx_rejected_too_late = 0;
    uint32_t cp_nb_tx_rejected_too_early = 0;
    uint32_t cp_nb_beacon_queued = 0;
    uint32_t cp_nb_beacon_sent = 0;
    uint32_t cp_nb_beacon_rejected = 0;

    /* GPS coordinates variables */ //gps坐标
    bool coord_ok = false;
    struct coord_s cp_gps_coord = {0.0, 0.0, 0}; //gps地址变量

    /* SX1302 data variables */
    uint32_t trig_tstamp;
    uint32_t inst_tstamp;
    uint64_t eui;
    float temperature;

    /* statistics variable */ //统计变量
    time_t t;
    char stat_timestamp[24]; //UTC time
    float rx_ok_ratio;
    float rx_bad_ratio;
    float rx_nocrc_ratio;
    float up_ack_ratio;
    float dw_ack_ratio;

    /* Parse command line options */ //输入命令行检查
    while( (i = getopt( argc, argv, "hc:" )) != -1 )
    {
        switch( i )
        {
        case 'h': //./lora_pkt_fwd -h
            usage( );
            return EXIT_SUCCESS;
            break;

        case 'c': //./lora_pkt_fwd -c global_conf.json
            conf_fname = optarg;
            break;

        default:
            printf( "ERROR: argument parsing options, use -h option for help\n" );
            usage( );
            return EXIT_FAILURE;
        }
    }

    /* display version informations */ //包转发程序运行显示
    MSG("*** Packet Forwarder ***\nVersion: " VERSION_STRING "\n"); //换行显示版本
    MSG("*** SX1302 HAL library version info ***\n%s\n***\n", lgw_version_info());

    /* display host endianness */
    #if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
        MSG("INFO: Little endian host\n");
    #elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
        MSG("INFO: Big endian host\n");
    #else
        MSG("INFO: Host endianness unknown\n");
    #endif

    /* load configuration files */ //调用上面的三大json解析函数
    if (access(conf_fname, R_OK) == 0) { /* if there is a global conf, parse it  */ //"global_conf.json"
        MSG("INFO: found configuration file %s, parsing it\n", conf_fname);
        x = parse_SX130x_configuration(conf_fname); //解析SX130x_conf对象
        if (x != 0) {
            exit(EXIT_FAILURE);
        }
        x = parse_gateway_configuration(conf_fname); //解析gateway_conf对象
        if (x != 0) {
            exit(EXIT_FAILURE);
        }
        x = parse_debug_configuration(conf_fname); //解析debug_conf对象
        if (x != 0) {
            MSG("INFO: no debug configuration\n");
        }
    } else {
        MSG("ERROR: [main] failed to find any configuration file named %s\n", conf_fname);
        exit(EXIT_FAILURE);
    }

    /* Start GPS a.s.a.p., to allow it to lock */ //a.s.a.p = as soon as possible
    if (gps_tty_path[0] != '\0') { /* do not try to open GPS device if no path set */ //网关是否启用gps的唯一标准（TTY: 硬件终端设备）
        i = lgw_gps_enable(gps_tty_path, "ubx7", 0, &gps_tty_fd); /* HAL only supports u-blox 7 for now */ //ublox7是一种商用gps模组
        if (i != LGW_GPS_SUCCESS) {
            printf("WARNING: [main] impossible to open %s for GPS sync (check permissions)\n", gps_tty_path);
            gps_enabled = false; //gps_enabled在这里由main直接判断
            gps_ref_valid = false;  //gps_ref_valid由thread_valid进一步判断
        } else {
            printf("INFO: [main] TTY port %s open for GPS synchronization\n", gps_tty_path);
            gps_enabled = true;
            gps_ref_valid = false;
        }
    }

    /* get timezone info */
    tzset(); //时间兼容函数

    /* sanity check on configuration variables */
    // TODO

    /* process some of the configuration variables */ //字节序
    net_mac_h = htonl((uint32_t)(0xFFFFFFFF & (lgwm>>32)));
    net_mac_l = htonl((uint32_t)(0xFFFFFFFF &  lgwm  ));

    /* prepare hints to open network sockets */ //既为upstream也为downstream打基础
    memset(&hints, 0, sizeof hints); //hints
    hints.ai_family = AF_INET; //IPV4 /* WA: Forcing IPv4 as AF_UNSPEC(IPV4 and IPV6) makes connection on localhost to fail */
    hints.ai_socktype = SOCK_DGRAM; //UDP

    /* look for server address w/ upstream port */
    i = getaddrinfo(serv_addr, serv_port_up, &hints, &result); 
	//serv_addr、serv_port_up由parse_gateway_configuration得出；从hints读取信息存储到result
	//因为IP + port -> socket
    if (i != 0) {
        MSG("ERROR: [up] getaddrinfo on address %s (PORT %s) returned %s\n", serv_addr, serv_port_up, gai_strerror(i));
        exit(EXIT_FAILURE);
    }

    /* try to open socket for upstream traffic */
    for (q=result; q!=NULL; q=q->ai_next) { //q指向result，q的属性都是上面getaddrinfo得到的；因为一个域名可能不止一个IP地址，所以，需要遍历res中的next，如下，是否还有下一个节点
        sock_up = socket(q->ai_family, q->ai_socktype,q->ai_protocol); //创建套接字sock_up，ai_protocol默认为0自动推演
        if (sock_up == -1) continue; /* try next field */
        else break; /* success, get out of loop */ //得到sock_up后跳出for循环，没有必要循环到结束条件q==NULL
    }
    if (q == NULL) { //一直循环到了结束条件q==NULL都没获得sock_up
        MSG("ERROR: [up] failed to open socket to any of server %s addresses (port %s)\n", serv_addr, serv_port_up);
        i = 1;
        for (q=result; q!=NULL; q=q->ai_next) {
            getnameinfo(q->ai_addr, q->ai_addrlen, host_name, sizeof host_name, port_name, sizeof port_name, NI_NUMERICHOST);
            //与getaddrinfo两级反转: socket -> IP + port
		    MSG("INFO: [up] result %i host:%s service:%s\n", i, host_name, port_name);
            ++i;
        }
        exit(EXIT_FAILURE); //异常退出程序
    }

    /* connect so we can send/receive packet with the server only */ 
    i = connect(sock_up, q->ai_addr, q->ai_addrlen); //连接上行socket；q为for循环break出时的值
    if (i != 0) {
        MSG("ERROR: [up] connect returned %s\n", strerror(errno));
        exit(EXIT_FAILURE);
    }
    freeaddrinfo(result); //释放掉好进行下行通信

    /* look for server address w/ downstream port */ //downstream是gateway与server通信，和device没关系
    i = getaddrinfo(serv_addr, serv_port_down, &hints, &result);
    if (i != 0) {
        MSG("ERROR: [down] getaddrinfo on address %s (port %s) returned %s\n", serv_addr, serv_port_down, gai_strerror(i));
        exit(EXIT_FAILURE);
    }

    /* try to open socket for downstream traffic */  //开启下行socket通信
    for (q=result; q!=NULL; q=q->ai_next) {
        sock_down = socket(q->ai_family, q->ai_socktype,q->ai_protocol);
        if (sock_down == -1) continue; /* try next field */
        else break; /* success, get out of loop */
    }
    if (q == NULL) {
        MSG("ERROR: [down] failed to open socket to any of server %s addresses (port %s)\n", serv_addr, serv_port_down);
        i = 1;
        for (q=result; q!=NULL; q=q->ai_next) {
            getnameinfo(q->ai_addr, q->ai_addrlen, host_name, sizeof host_name, port_name, sizeof port_name, NI_NUMERICHOST);
            MSG("INFO: [down] result %i host:%s service:%s\n", i, host_name, port_name);
            ++i;
        }
        exit(EXIT_FAILURE);
    }

    /* connect so we can send/receive packet with the server only */
    i = connect(sock_down, q->ai_addr, q->ai_addrlen);
    if (i != 0) {
        MSG("ERROR: [down] connect returned %s\n", strerror(errno));
        exit(EXIT_FAILURE);
    }
    freeaddrinfo(result);

    if (com_type == LGW_COM_SPI) {
        /* Board reset */ //执行reset_lgw.sh脚本
        if (system("./reset_lgw.sh start") != 0) {
            printf("ERROR: failed to reset SX1302, check your reset_lgw.sh script\n");
            exit(EXIT_FAILURE);
        }
    }

    for (l = 0; l < LGW_IF_CHAIN_NB; l++) {
        for (m = 0; m < 8; m++) {
            nb_pkt_log[l][m] = 0; //初始化
        }
    }

    /* starting the concentrator */ //运行固定显示倒数第二句
    i = lgw_start();
    if (i == LGW_HAL_SUCCESS) {
        MSG("INFO: [main] concentrator started, packet can now be received\n");
    } else {
        MSG("ERROR: [main] failed to start the concentrator\n");
        exit(EXIT_FAILURE);
    }

    /* get the concentrator EUI */ //Gateway ID\GwEUI，//运行固定显示最后一句
    i = lgw_get_eui(&eui);
    if (i != LGW_HAL_SUCCESS) {
        printf("ERROR: failed to get concentrator EUI\n");
    } else {
        printf("INFO: concentrator EUI: 0x%016" PRIx64 "\n", eui);
    }

    /* spawn threads to manage upstream and downstream */
    i = pthread_create(&thrid_up, NULL, (void * (*)(void *))thread_up, NULL);
    if (i != 0) {
        MSG("ERROR: [main] impossible to create upstream thread\n");
        exit(EXIT_FAILURE);
    }
    i = pthread_create(&thrid_down, NULL, (void * (*)(void *))thread_down, NULL);
    if (i != 0) {
        MSG("ERROR: [main] impossible to create downstream thread\n");
        exit(EXIT_FAILURE);
    }
    i = pthread_create(&thrid_jit, NULL, (void * (*)(void *))thread_jit, NULL);
    if (i != 0) {
        MSG("ERROR: [main] impossible to create JIT thread\n");
        exit(EXIT_FAILURE);
    }

    /* spawn thread for background spectral scan */
    if (spectral_scan_params.enable == true) {
        i = pthread_create(&thrid_ss, NULL, (void * (*)(void *))thread_spectral_scan, NULL);
        if (i != 0) {
            MSG("ERROR: [main] impossible to create Spectral Scan thread\n");
            exit(EXIT_FAILURE);
        }
    }

    /* spawn thread to manage GPS */
    if (gps_enabled == true) {
        i = pthread_create(&thrid_gps, NULL, (void * (*)(void *))thread_gps, NULL);
        if (i != 0) {
            MSG("ERROR: [main] impossible to create GPS thread\n");
            exit(EXIT_FAILURE);
        }
        i = pthread_create(&thrid_valid, NULL, (void * (*)(void *))thread_valid, NULL);
        if (i != 0) {
            MSG("ERROR: [main] impossible to create validation thread\n");
            exit(EXIT_FAILURE);
        }
    }

    /* configure signal handling */ //调用sig_handler
    sigemptyset(&sigact.sa_mask);
    sigact.sa_flags = 0;
    sigact.sa_handler = sig_handler;
    sigaction(SIGQUIT, &sigact, NULL); /* Ctrl-\ */
    sigaction(SIGINT, &sigact, NULL); /* Ctrl-C */
    sigaction(SIGTERM, &sigact, NULL); /* default "kill" command */

    /* main loop task : statistics collection */ //所有threads得到的统计信息
    while (!exit_sig && !quit_sig) { //当不手动停止时
        /* wait for next reporting interval */
        wait_ms(1000 * stat_interval);

        /* get timestamp for statistics */
        t = time(NULL);
        strftime(stat_timestamp, sizeof stat_timestamp, "%F %T %Z", gmtime(&t)); //get UTC time without GPS

        /* access upstream statistics, copy and reset them */ //上行数据统计
        pthread_mutex_lock(&mx_meas_up);
        cp_nb_rx_rcv       = meas_nb_rx_rcv;
        cp_nb_rx_ok        = meas_nb_rx_ok;
        cp_nb_rx_bad       = meas_nb_rx_bad;
        cp_nb_rx_nocrc     = meas_nb_rx_nocrc;
        cp_up_pkt_fwd      = meas_up_pkt_fwd;
        cp_up_network_byte = meas_up_network_byte;
        cp_up_payload_byte = meas_up_payload_byte;
        cp_up_dgram_sent   = meas_up_dgram_sent;
        cp_up_ack_rcv      = meas_up_ack_rcv;
        meas_nb_rx_rcv = 0;
        meas_nb_rx_ok = 0;
        meas_nb_rx_bad = 0;
        meas_nb_rx_nocrc = 0;
        meas_up_pkt_fwd = 0;
        meas_up_network_byte = 0;
        meas_up_payload_byte = 0;
        meas_up_dgram_sent = 0;
        meas_up_ack_rcv = 0;
        pthread_mutex_unlock(&mx_meas_up);
        if (cp_nb_rx_rcv > 0) {
            rx_ok_ratio = (float)cp_nb_rx_ok / (float)cp_nb_rx_rcv;
            rx_bad_ratio = (float)cp_nb_rx_bad / (float)cp_nb_rx_rcv;
            rx_nocrc_ratio = (float)cp_nb_rx_nocrc / (float)cp_nb_rx_rcv;
        } else {
            rx_ok_ratio = 0.0;
            rx_bad_ratio = 0.0;
            rx_nocrc_ratio = 0.0;
        }
        if (cp_up_dgram_sent > 0) {
            up_ack_ratio = (float)cp_up_ack_rcv / (float)cp_up_dgram_sent;
        } else {
            up_ack_ratio = 0.0;
        }

        /* access downstream statistics, copy and reset them */ //下行数据统计
        pthread_mutex_lock(&mx_meas_dw);
		//thread_down + thread_jit
        cp_dw_pull_sent    =  meas_dw_pull_sent;
        cp_dw_ack_rcv      =  meas_dw_ack_rcv;
        cp_dw_dgram_rcv    =  meas_dw_dgram_rcv;
        cp_dw_network_byte =  meas_dw_network_byte;
        cp_dw_payload_byte =  meas_dw_payload_byte;
        cp_nb_tx_ok        =  meas_nb_tx_ok;
        cp_nb_tx_fail      =  meas_nb_tx_fail;
        cp_nb_tx_requested                 +=  meas_nb_tx_requested;
        cp_nb_tx_rejected_collision_packet +=  meas_nb_tx_rejected_collision_packet;
        cp_nb_tx_rejected_collision_beacon +=  meas_nb_tx_rejected_collision_beacon;
        cp_nb_tx_rejected_too_late         +=  meas_nb_tx_rejected_too_late;
        cp_nb_tx_rejected_too_early        +=  meas_nb_tx_rejected_too_early;
        cp_nb_beacon_queued   +=  meas_nb_beacon_queued;
        cp_nb_beacon_sent     +=  meas_nb_beacon_sent;
        cp_nb_beacon_rejected +=  meas_nb_beacon_rejected;
        meas_dw_pull_sent = 0;
        meas_dw_ack_rcv = 0;
        meas_dw_dgram_rcv = 0;
        meas_dw_network_byte = 0;
        meas_dw_payload_byte = 0;
        meas_nb_tx_ok = 0;
        meas_nb_tx_fail = 0;
        meas_nb_tx_requested = 0;
        meas_nb_tx_rejected_collision_packet = 0;
        meas_nb_tx_rejected_collision_beacon = 0;
        meas_nb_tx_rejected_too_late = 0;
        meas_nb_tx_rejected_too_early = 0;
        meas_nb_beacon_queued = 0;
        meas_nb_beacon_sent = 0;
        meas_nb_beacon_rejected = 0;
        pthread_mutex_unlock(&mx_meas_dw);
        if (cp_dw_pull_sent > 0) {
            dw_ack_ratio = (float)cp_dw_ack_rcv / (float)cp_dw_pull_sent;
        } else {
            dw_ack_ratio = 0.0;
        }

		//GPS是否启用对后面报告显示有影响
        /* access GPS statistics, copy them */ //真gps
        if (gps_enabled == true) {
            pthread_mutex_lock(&mx_meas_gps);
            coord_ok = gps_coord_valid; //reference可用
            cp_gps_coord = meas_gps_coord; 
            pthread_mutex_unlock(&mx_meas_gps);
        }

        /* overwrite with reference coordinates if function is enabled */ //fake gps
        if (gps_fake_enable == true) {
            cp_gps_coord = reference_coord; //采用global.config里的reference_coord作为fake gps location
        }

        /* display a report */
        printf("\n##### %s #####\n", stat_timestamp); //stat_timestamp：目前的格林威治时间
        printf("### [UPSTREAM] ###\n");
        printf("# RF packets received by concentrator: %u\n", cp_nb_rx_rcv);
        printf("# CRC_OK: %.2f%%, CRC_FAIL: %.2f%%, NO_CRC: %.2f%%\n", 100.0 * rx_ok_ratio, 100.0 * rx_bad_ratio, 100.0 * rx_nocrc_ratio);
        printf("# RF packets forwarded: %u (%u bytes)\n", cp_up_pkt_fwd, cp_up_payload_byte);
        printf("# PUSH_DATA datagrams sent: %u (%u bytes)\n", cp_up_dgram_sent, cp_up_network_byte);
        printf("# PUSH_DATA acknowledged: %.2f%%\n", 100.0 * up_ack_ratio);
        printf("### [DOWNSTREAM] ###\n");
        printf("# PULL_DATA sent: %u (%.2f%% acknowledged)\n", cp_dw_pull_sent, 100.0 * dw_ack_ratio);
        printf("# PULL_RESP(onse) datagrams received: %u (%u bytes)\n", cp_dw_dgram_rcv, cp_dw_network_byte);
        printf("# RF packets sent to concentrator: %u (%u bytes)\n", (cp_nb_tx_ok+cp_nb_tx_fail), cp_dw_payload_byte);
        printf("# TX errors: %u\n", cp_nb_tx_fail);
        if (cp_nb_tx_requested != 0 ) {
            printf("# TX rejected (collision packet): %.2f%% (req:%u, rej:%u)\n", 100.0 * cp_nb_tx_rejected_collision_packet / cp_nb_tx_requested, cp_nb_tx_requested, cp_nb_tx_rejected_collision_packet);
            printf("# TX rejected (collision beacon): %.2f%% (req:%u, rej:%u)\n", 100.0 * cp_nb_tx_rejected_collision_beacon / cp_nb_tx_requested, cp_nb_tx_requested, cp_nb_tx_rejected_collision_beacon);
            printf("# TX rejected (too late): %.2f%% (req:%u, rej:%u)\n", 100.0 * cp_nb_tx_rejected_too_late / cp_nb_tx_requested, cp_nb_tx_requested, cp_nb_tx_rejected_too_late);
            printf("# TX rejected (too early): %.2f%% (req:%u, rej:%u)\n", 100.0 * cp_nb_tx_rejected_too_early / cp_nb_tx_requested, cp_nb_tx_requested, cp_nb_tx_rejected_too_early);
        }
        printf("### SX1302 Status ###\n");
        pthread_mutex_lock(&mx_concent);
        i  = lgw_get_instcnt(&inst_tstamp); //SX1302新出的，SX1301没有；Get concentrator count用于jit_enqueue/jit_peek
        i |= lgw_get_trigcnt(&trig_tstamp); //|=按位或；Get PPM pulse concentrator count用于lgw_gps_sync
        //总的来说，count从upstream得到，用于downstream
		pthread_mutex_unlock(&mx_concent);
        if (i != LGW_HAL_SUCCESS) { //lgw_get_instcnt与lgw_get_trigcnt至少有一个未成功
            printf("# SX1302 counter unknown\n");
        } else {
            printf("# SX1302 counter (INST): %u\n", inst_tstamp); //SX1302新出的，SX1301没有
            printf("# SX1302 counter (PPS):  %u\n", trig_tstamp);
        }
        printf("# BEACON queued: %u\n", cp_nb_beacon_queued);
        printf("# BEACON sent so far: %u\n", cp_nb_beacon_sent);
        printf("# BEACON rejected: %u\n", cp_nb_beacon_rejected);
        printf("### [JIT] ###\n");
        /* get timestamp captured on PPM pulse  */
        jit_print_queue (&jit_queue[0], false, DEBUG_LOG);
        printf("#--------\n");
        jit_print_queue (&jit_queue[1], false, DEBUG_LOG);
        printf("### [GPS] ###\n");
        if (gps_enabled == true) { //启用gps
            /* no need for mutex, display is not critical */
            if (gps_ref_valid == true) { //thread_valid启用gps参考时间
                printf("# Valid time reference (age: %li sec)\n", (long)difftime(time(NULL), time_reference_gps.systime));
            } else {
                printf("# Invalid time reference (age: %li sec)\n", (long)difftime(time(NULL), time_reference_gps.systime));
            }
            if (coord_ok == true) { //启用gps地址
                printf("# GPS coordinates: latitude %.5f, longitude %.5f, altitude %i m\n", cp_gps_coord.lat, cp_gps_coord.lon, cp_gps_coord.alt);
            } else {
                printf("# no valid GPS coordinates available yet\n");
            }
        } else if (gps_fake_enable == true) {  //启用假gps
            printf("# GPS *FAKE* coordinates: latitude %.5f, longitude %.5f, altitude %i m\n", cp_gps_coord.lat, cp_gps_coord.lon, cp_gps_coord.alt);
        } else { //未启用gps
            printf("# GPS sync is disabled\n");
        }
        pthread_mutex_lock(&mx_concent);
        i = lgw_get_temperature(&temperature); //温度
        pthread_mutex_unlock(&mx_concent);
        if (i != LGW_HAL_SUCCESS) {
            printf("### Concentrator temperature unknown ###\n");
        } else {
            printf("### Concentrator temperature: %.0f C ###\n", temperature);
        }
        printf("##### END #####\n");

        /* generate a JSON report (will be sent to server by upstream thread) */ //Upstream JSON data structure "stat" object
        pthread_mutex_lock(&mx_stat_rep);
        if (((gps_enabled == true) && (coord_ok == true)) || (gps_fake_enable == true)) { //GPS位置合理的真GPS或直接使用假GPS
            snprintf(status_report, STATUS_SIZE, "\"stat\":{\"time\":\"%s\",\"lati\":%.5f,\"long\":%.5f,\"alti\":%i,\"rxnb\":%u,\"rxok\":%u,\"rxfw\":%u,\"ackr\":%.1f,\"dwnb\":%u,\"txnb\":%u,\"temp\":%.1f}", stat_timestamp, cp_gps_coord.lat, cp_gps_coord.lon, cp_gps_coord.alt, cp_nb_rx_rcv, cp_nb_rx_ok, cp_up_pkt_fwd, 100.0 * up_ack_ratio, cp_dw_dgram_rcv, cp_nb_tx_ok, temperature);
        } else {
            snprintf(status_report, STATUS_SIZE, "\"stat\":{\"time\":\"%s\",\"rxnb\":%u,\"rxok\":%u,\"rxfw\":%u,\"ackr\":%.1f,\"dwnb\":%u,\"txnb\":%u,\"temp\":%.1f}", stat_timestamp, cp_nb_rx_rcv, cp_nb_rx_ok, cp_up_pkt_fwd, 100.0 * up_ack_ratio, cp_dw_dgram_rcv, cp_nb_tx_ok, temperature);
        }
        report_ready = true; //there is a new report to send to the server
        pthread_mutex_unlock(&mx_stat_rep);
    }

    //手动停止程序后
    /* wait for all threads with a COM with the concentrator board to finish (1 fetch cycle max) */
    i = pthread_join(thrid_up, NULL); //以阻塞的方式等待thread_up结束
    if (i != 0) {
        printf("ERROR: failed to join upstream thread with %d - %s\n", i, strerror(errno));
    }
    i = pthread_join(thrid_down, NULL);
    if (i != 0) {
        printf("ERROR: failed to join downstream thread with %d - %s\n", i, strerror(errno));
    }
    i = pthread_join(thrid_jit, NULL);
    if (i != 0) {
        printf("ERROR: failed to join JIT thread with %d - %s\n", i, strerror(errno));
    }
    if (spectral_scan_params.enable == true) {
        i = pthread_join(thrid_ss, NULL);
        if (i != 0) {
            printf("ERROR: failed to join Spectral Scan thread with %d - %s\n", i, strerror(errno));
        }
    }
    if (gps_enabled == true) {
        pthread_cancel(thrid_gps); /* don't wait for GPS thread, no access to concentrator board */
        pthread_cancel(thrid_valid); /* don't wait for validation thread, no access to concentrator board */

        i = lgw_gps_disable(gps_tty_fd);
        if (i == LGW_HAL_SUCCESS) {
            MSG("INFO: GPS closed successfully\n");
        } else {
            MSG("WARNING: failed to close GPS successfully\n");
        }
    }

    /* if an exit signal was received, try to quit properly */ //关闭程序
    if (exit_sig) {
        /* shut down network sockets */
        shutdown(sock_up, SHUT_RDWR);
        shutdown(sock_down, SHUT_RDWR);
        /* stop the hardware */
        i = lgw_stop();
        if (i == LGW_HAL_SUCCESS) {
            MSG("INFO: concentrator stopped successfully\n");
        } else {
            MSG("WARNING: failed to stop concentrator successfully\n");
        }
    }

    if (com_type == LGW_COM_SPI) {
        /* Board reset */
        if (system("./reset_lgw.sh stop") != 0) {
            printf("ERROR: failed to reset SX1302, check your reset_lgw.sh script\n");
            exit(EXIT_FAILURE);
        }
    }

    MSG("INFO: Exiting packet forwarder program\n");
    exit(EXIT_SUCCESS);
}

/* -------------------------------------------------------------------------- */
/* --- THREAD 1: RECEIVING PACKETS AND FORWARDING THEM ---------------------- */

void thread_up(void) { //PUSH_DATA packet
    int i, j, k; /* loop variables */
    unsigned pkt_in_dgram; /* nb on Lora packet in the current datagram */
    char stat_timestamp[24]; //UTC time
    time_t t;

    /* allocate memory for packet fetching and processing */
    struct lgw_pkt_rx_s rxpkt[NB_PKT_MAX]; /* array containing inbound packets + metadata */
    struct lgw_pkt_rx_s *p; /* pointer on a RX packet */ //Gateway从Node接收到的数据包，代指rxpkt
    int nb_pkt; //number of packets retrieved

    /* local copy of GPS time reference */
    bool ref_ok = false; /* determine if GPS time reference must be used or not */ //GPS reference
    struct tref local_ref; /* time reference used for UTC <-> timestamp conversion */ //提供时间转换的参考

    /* data buffers */
    uint8_t buff_up[TX_BUFF_SIZE]; /* buffer to compose the upstream packet */
    int buff_index;
    uint8_t buff_ack[32]; /* buffer to receive acknowledges */

    /* protocol variables */
    uint8_t token_h; /* random token for acknowledgement matching */ //用于PUSH_ACK
    uint8_t token_l; /* random token for acknowledgement matching */

    /* ping measurement variables */
    struct timespec send_time;
    struct timespec recv_time;

    /* GPS synchronization variables */
    struct timespec pkt_utc_time; //UTC absolute times
    struct tm * x; /* broken-up UTC time */
    struct timespec pkt_gps_time; //GPS absolute time
    uint64_t pkt_gps_time_ms;

    /* report management variable */ //stat
    bool send_report = false;

    /* mote info variables */ //End Device
    uint32_t mote_addr = 0; //unsigned int 
    uint16_t mote_fcnt = 0;

    /* set upstream socket RX timeout */ //接收时限套接字超时
    i = setsockopt(sock_up, SOL_SOCKET, SO_RCVTIMEO, (void *)&push_timeout_half, sizeof push_timeout_half);
    if (i != 0) {
        MSG("ERROR: [up] setsockopt returned %s\n", strerror(errno));
        exit(EXIT_FAILURE);
    }

    /* pre-fill the data buffer with fixed fields */ //PUSH_DATA packet
    buff_up[0] = PROTOCOL_VERSION; //protocol version = 2
    buff_up[3] = PKT_PUSH_DATA; //PUSH_DATA identifier 0x00
    *(uint32_t *)(buff_up + 4) = net_mac_h; //Gateway unique identifier (MAC address)
    *(uint32_t *)(buff_up + 8) = net_mac_l;

    while (!exit_sig && !quit_sig) { //未得到退出信号就一直进行

        /* fetch packets */
        pthread_mutex_lock(&mx_concent);
        nb_pkt = lgw_receive(NB_PKT_MAX, rxpkt); //从Node接受最多NB_PKT_MAX个数据包，rxpkt pointer to an array of struct that will receive the packet metadata and payload pointers
        pthread_mutex_unlock(&mx_concent);
        if (nb_pkt == LGW_HAL_ERROR) {
            MSG("ERROR: [up] failed packet fetch, exiting\n");
            exit(EXIT_FAILURE);
        }

        /* check if there are status report to send */
        send_report = report_ready; /* copy the variable so it doesn't change mid-function */
        /* no mutex, we're only reading */

        /* wait a short time if no packets, nor status report */
        if ((nb_pkt == 0) && (send_report == false)) {
            wait_ms(FETCH_SLEEP_MS); //退出本轮循环
            continue;
        }

        /* get a copy of GPS time reference (avoid 1 mutex per packet) */ //为Packet RX time (GPS based)做准备
        if ((nb_pkt > 0) && (gps_enabled == true)) { //要获得gps reference time必须启用gps
            pthread_mutex_lock(&mx_timeref);
            ref_ok = gps_ref_valid; //thread_valid启用gps reference
            local_ref = time_reference_gps; //thread_gps获得时间转换的参考
            pthread_mutex_unlock(&mx_timeref);
        } else {
            ref_ok = false;
        }

        /* get timestamp for statistics */ //时间戳：只有DEBUG才有用
        t = time(NULL);
        strftime(stat_timestamp, sizeof stat_timestamp, "%F %T %Z", gmtime(&t)); //get UTC time without GPS
        MSG_DEBUG(DEBUG_PKT_FWD, "\nCurrent time: %s \n", stat_timestamp); //stat_timestamp：目前的格林威治时间；只有DEBUG才输出这句

        /* start composing datagram with the header */
        token_h = (uint8_t)rand(); /* random token */ //random token
        token_l = (uint8_t)rand(); /* random token */
        buff_up[1] = token_h;
        buff_up[2] = token_l;
        buff_index = 12; /* 12-byte header */

        /* start of JSON structure */ //Upstream JSON data structure //datagram
        memcpy((void *)(buff_up + buff_index), (void *)"{\"rxpk\":[", 9);
        buff_index += 9;

        /* serialize Lora packets metadata and payload */
        pkt_in_dgram = 0; //初始化datagram中的packet数量为0；packet排列成datagram：每个{}是一个packet，[...]是一个datagram
        for (i = 0; i < nb_pkt; ++i) {
            p = &rxpkt[i]; //rxpkt[i]接收到的第i个数据包datagram

            //由接收测试与在线解码比对可得到p->payload = PHYPayload，只从在线解码也可以得到
            /* Get mote information from current packet (addr, fcnt) */ //mote information：end device的信息
            /* FHDR - DevAddr */ //mote_addr: DevAddr[4 bytes]
		    //字节序：Little Endian to Big Endian
            if (p->size >= 8) {
                mote_addr  = p->payload[1];  //从PHYPayload的第二个字节开始，也就是MACPayload开始
                mote_addr |= p->payload[2] << 8; 
                mote_addr |= p->payload[3] << 16;
                mote_addr |= p->payload[4] << 24;
                /* FHDR - FCnt */ //mote_fcnt: FCnt[2 bytes]: 终端节点重新入网/启动后重置，且数值由节点发送次数决定，与网关无关
                mote_fcnt  = p->payload[6];
                mote_fcnt |= p->payload[7] << 8;
            } else {
                mote_addr = 0;
                mote_fcnt = 0;
            }

            /* basic packet filtering */ //crc判定
            pthread_mutex_lock(&mx_meas_up);
            meas_nb_rx_rcv += 1;
            switch(p->status) {
                case STAT_CRC_OK:
                    meas_nb_rx_ok += 1;
                    if (!fwd_valid_pkt) { //此情况下根据gobal.config，即使crc正确也不转发给NS
                        pthread_mutex_unlock(&mx_meas_up);
                        continue; /* skip that packet */ //如果这个switch是在一个循环中,switch中出现的continue其实是对这个循环做控制的
                    }
                    break; //switch-break
                case STAT_CRC_BAD:
                    meas_nb_rx_bad += 1;
                    if (!fwd_error_pkt) {
                        pthread_mutex_unlock(&mx_meas_up);
                        continue; /* skip that packet */
                    }
                    break;
                case STAT_NO_CRC:
                    meas_nb_rx_nocrc += 1;
                    if (!fwd_nocrc_pkt) {
                        pthread_mutex_unlock(&mx_meas_up);
                        continue; /* skip that packet */
                    }
                    break;
                default:
                    MSG("WARNING: [up] received packet with unknown status %u (size %u, modulation %u, BW %u, DR %u, RSSI %.1f)\n", p->status, p->size, p->modulation, p->bandwidth, p->datarate, p->rssic);
                    pthread_mutex_unlock(&mx_meas_up);
                    continue; /* skip that packet */
                    // exit(EXIT_FAILURE);
            }

			//只有可以转发的数据包才能出现在json up消息里
            meas_up_pkt_fwd += 1; //RF packets forwarded
            meas_up_payload_byte += p->size; //RF packets forwarded size: 在线解码得到的LoRa包结构中的PHYPayload大小
            pthread_mutex_unlock(&mx_meas_up);
            printf( "\nINFO: Received pkt from mote: %08X (fcnt=%u)\n", mote_addr, mote_fcnt );

            /* Start of packet, add inter-packet separator if necessary */ //{"jver":*,...,"data":""}为一个packet
            if (pkt_in_dgram == 0) { //for循环的第一轮循环，即datagram里的第一个packet
                buff_up[buff_index] = '{';
                ++buff_index;
            } else { //inter-packet separator //JSON up: {"rxpk":[{},...,{}]}，每个{}是一个packet，大多出现于crc_bad也可转发时
                buff_up[buff_index] = ',';
                buff_up[buff_index+1] = '{';
                buff_index += 2;				
				//如JSON up: {"rxpk":[{"jver":1,"tmst":195151122,"chan":5,"rfch":1,"freq":476.400000,"mid": 2,"stat":1,"modu":"LORA","datr":"SF12BW125","codr":"4/5","rssis":-80,"lsnr":-0.8,"foff":507,"rssi":-77,"size":25,"data":"gQwgUBMAEwATAKGyw9TloaKjpKWmp6ipqg=="},
									//{"jver":1,"tmst":195151172,"chan":7,"rfch":1,"freq":476.800000,"mid": 0,"stat":-1,"modu":"LORA","datr":"SF12BW125","codr":"4/5","rssis":-62,"lsnr":-8.8,"foff":25539,"rssi":-54,"size":25,"data":"gQwgUBMBE8CzgDEXWtQlqaKjoeDGovj6ww=="}]}
            }

            /* JSON rxpk frame format version, 8 useful chars */ //Upstream JSON data structure
            j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, "\"jver\":%d", PROTOCOL_JSON_RXPK_FRAME_FORMAT );
            if (j > 0) {
                buff_index += j;
            } else {
                MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                exit(EXIT_FAILURE);
            }

            /* RAW timestamp, 8-17 useful chars */ //内部晶振相对时间戳timestamp
            //把tmst对象添加到buff_up
            j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"tmst\":%u", p->count_us);
            if (j > 0) {
                buff_index += j;
            } else {
                MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                exit(EXIT_FAILURE);
            }

            /* Packet RX time (GPS based), 37 useful chars */ //获得绝对时间
            if (ref_ok == true) { //get a copy of GPS time reference必须要成功
                /* convert packet timestamp to UTC absolute time */ //timestamp -> UTC time；即p->count_us -> pkt_utc_time
                j = lgw_cnt2utc(local_ref, p->count_us, &pkt_utc_time);
                if (j == LGW_GPS_SUCCESS) {
                    /* split the UNIX timestamp to its calendar components */
                    x = gmtime(&(pkt_utc_time.tv_sec));
                    //convert a SX1302 counter value to GPS UTC time when we receive an uplink, in order to fill the “time” field of JSON “rxpk” structure
                    j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"time\":\"%04i-%02i-%02iT%02i:%02i:%02i.%06liZ\"", (x->tm_year)+1900, (x->tm_mon)+1, x->tm_mday, x->tm_hour, x->tm_min, x->tm_sec, (pkt_utc_time.tv_nsec)/1000); /* ISO 8601 format */
                    if (j > 0) {
                        buff_index += j;
                    } else {
                        MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                        exit(EXIT_FAILURE);
                    }
                }
                /* convert packet timestamp to GPS absolute time */ //timestamp -> GPS time；即p->count_us -> pkt_gps_time
                j = lgw_cnt2gps(local_ref, p->count_us, &pkt_gps_time);
                if (j == LGW_GPS_SUCCESS) {
                    pkt_gps_time_ms = pkt_gps_time.tv_sec * 1E3 + pkt_gps_time.tv_nsec / 1E6;
				    //把tmms对象添加到buff_up
                    j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"tmms\":%" PRIu64 "", pkt_gps_time_ms); /* GPS time in milliseconds since 06.Jan.1980 */
                    if (j > 0) {
                        buff_index += j;
                    } else {
                        MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                        exit(EXIT_FAILURE);
                    }
                }
            }

			//get UTC time without GPS

			char time0[100] = "\"";
			char time1[100];
			char time2[100];
			char time3[100] = ".000000000Z\""; //毫秒部分弄个固定值，反正不重要，也得不到
	
			sscanf(stat_timestamp, "%s", time1); //将字符串类型转化为ISO 8601格式
			sscanf(stat_timestamp, "%*s%s", time2);
            strcat(time0,time1);
			strcat(time0,"T");
			strcat(time0,time2);
			strcat(time0,time3);
            j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"time\":%s", time0); //stat_timestamp是字符串类型，即使在这里成功插入了buff_up也会因为不是ISO 8601格式而不被NS接收，从而没有PUSH_ACK返回
            if (j > 0) {
                buff_index += j;
            } else {
                MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                exit(EXIT_FAILURE);
            }
			
            /* Fine timestamp */
            if (p->ftime_received == true) {
                j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"ftime\":%u", p->ftime);
                if (j > 0) {
                    buff_index += j;
                } else {
                    MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                    exit(EXIT_FAILURE);
                }
            }

            /* Packet concentrator channel, RF chain & RX frequency, 34-36 useful chars */ //Packet concentrator channel = IF chain
            j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"chan\":%1u,\"rfch\":%1u,\"freq\":%.6lf,\"mid\":%2u", p->if_chain, p->rf_chain, ((double)p->freq_hz / 1e6), p->modem_id);
            if (j > 0) {
                buff_index += j;
            } else {
                MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                exit(EXIT_FAILURE);
            }

            /* Packet status, 9-10 useful chars */ //CRC；通过接收检测程序可以发现可以通过p->crc输出crc16具体值例如0xD228
            switch (p->status) {
                case STAT_CRC_OK:
                    memcpy((void *)(buff_up + buff_index), (void *)",\"stat\":1", 9);
                    buff_index += 9;
                    break;
                case STAT_CRC_BAD:
                    memcpy((void *)(buff_up + buff_index), (void *)",\"stat\":-1", 10);
                    buff_index += 10;
                    break;
                case STAT_NO_CRC:
                    memcpy((void *)(buff_up + buff_index), (void *)",\"stat\":0", 9);
                    buff_index += 9;
                    break;
                default:
                    MSG("ERROR: [up] received packet with unknown status 0x%02X\n", p->status);
                    memcpy((void *)(buff_up + buff_index), (void *)",\"stat\":?", 9);
                    buff_index += 9;
                    exit(EXIT_FAILURE);
            }

            /* Packet modulation, 13-14 useful chars */
            if (p->modulation == MOD_LORA) {
                memcpy((void *)(buff_up + buff_index), (void *)",\"modu\":\"LORA\"", 14);
                buff_index += 14;

                /* Lora datarate & bandwidth, 16-19 useful chars */
                switch (p->datarate) {
                    case DR_LORA_SF5:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF5", 12);
                        buff_index += 12;
                        break;
                    case DR_LORA_SF6:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF6", 12);
                        buff_index += 12;
                        break;
                    case DR_LORA_SF7:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF7", 12);
                        buff_index += 12;
                        break;
                    case DR_LORA_SF8:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF8", 12);
                        buff_index += 12;
                        break;
                    case DR_LORA_SF9:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF9", 12);
                        buff_index += 12;
                        break;
                    case DR_LORA_SF10:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF10", 13);
                        buff_index += 13;
                        break;
                    case DR_LORA_SF11:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF11", 13);
                        buff_index += 13;
                        break;
                    case DR_LORA_SF12:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF12", 13);
                        buff_index += 13;
                        break;
                    default:
                        MSG("ERROR: [up] lora packet with unknown datarate 0x%02X\n", p->datarate);
                        memcpy((void *)(buff_up + buff_index), (void *)",\"datr\":\"SF?", 12);
                        buff_index += 12;
                        exit(EXIT_FAILURE);
                }
                switch (p->bandwidth) {
                    case BW_125KHZ:
                        memcpy((void *)(buff_up + buff_index), (void *)"BW125\"", 6);
                        buff_index += 6;
                        break;
                    case BW_250KHZ:
                        memcpy((void *)(buff_up + buff_index), (void *)"BW250\"", 6);
                        buff_index += 6;
                        break;
                    case BW_500KHZ:
                        memcpy((void *)(buff_up + buff_index), (void *)"BW500\"", 6);
                        buff_index += 6;
                        break;
                    default:
                        MSG("ERROR: [up] lora packet with unknown bandwidth 0x%02X\n", p->bandwidth);
                        memcpy((void *)(buff_up + buff_index), (void *)"BW?\"", 4);
                        buff_index += 4;
                        exit(EXIT_FAILURE);
                }

                /* Packet ECC coding rate, 11-13 useful chars */ //纠错码/编码率
                switch (p->coderate) {
                    case CR_LORA_4_5:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"codr\":\"4/5\"", 13);
                        buff_index += 13;
                        break;
                    case CR_LORA_4_6:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"codr\":\"4/6\"", 13);
                        buff_index += 13;
                        break;
                    case CR_LORA_4_7:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"codr\":\"4/7\"", 13);
                        buff_index += 13;
                        break;
                    case CR_LORA_4_8:
                        memcpy((void *)(buff_up + buff_index), (void *)",\"codr\":\"4/8\"", 13);
                        buff_index += 13;
                        break;
                    case 0: /* treat the CR0 case (mostly false sync) */
                        memcpy((void *)(buff_up + buff_index), (void *)",\"codr\":\"OFF\"", 13);
                        buff_index += 13;
                        break;
                    default:
                        MSG("ERROR: [up] lora packet with unknown coderate 0x%02X\n", p->coderate);
                        memcpy((void *)(buff_up + buff_index), (void *)",\"codr\":\"?\"", 11);
                        buff_index += 11;
                        exit(EXIT_FAILURE);
                }

                /* Signal RSSI, payload size */
                j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"rssis\":%.0f", roundf(p->rssis));
                if (j > 0) {
                    buff_index += j;
                } else {
                    MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                    exit(EXIT_FAILURE);
                }

                /* Lora SNR */
                j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"lsnr\":%.1f", p->snr);
                if (j > 0) {
                    buff_index += j;
                } else {
                    MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                    exit(EXIT_FAILURE);
                }

                /* Lora frequency offset */
                j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"foff\":%d", p->freq_offset);
                if (j > 0) {
                    buff_index += j;
                } else {
                    MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                    exit(EXIT_FAILURE);
                }
            } else if (p->modulation == MOD_FSK) {
                memcpy((void *)(buff_up + buff_index), (void *)",\"modu\":\"FSK\"", 13);
                buff_index += 13;

                /* FSK datarate, 11-14 useful chars */ //频率偏移调制/频移键控
                j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"datr\":%u", p->datarate);
                if (j > 0) {
                    buff_index += j;
                } else {
                    MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                    exit(EXIT_FAILURE);
                }
            } else {
                MSG("ERROR: [up] received packet with unknown modulation 0x%02X\n", p->modulation);
                exit(EXIT_FAILURE);
            }

            /* Channel RSSI, payload size, 18-23 useful chars */
            j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, ",\"rssi\":%.0f,\"size\":%u", roundf(p->rssic), p->size);
            if (j > 0) {
                buff_index += j;
            } else {
                MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 4));
                exit(EXIT_FAILURE);
            }

            /* Packet base64-encoded payload, 14-350 useful chars */ //base64编码
            memcpy((void *)(buff_up + buff_index), (void *)",\"data\":\"", 9);
            buff_index += 9;
			//rxpkt->payload使用base64加密: p->payload (PHYPayload) 到 data
            j = bin_to_b64(p->payload, p->size, (char *)(buff_up + buff_index), 341); /* 255 bytes = 340 chars in b64 + null char */

			//printf("PHYPayload: "); //copy接收测试以确定发送的p->payload = PHYPayload
            //for(int count = 0; count < p->size; count++){
            //printf("%02X", p->payload[count]);
            //}
            //printf("\n");
            
            if (j>=0) {
                buff_index += j;
            } else {
                MSG("ERROR: [up] bin_to_b64 failed line %u\n", (__LINE__ - 5));
                exit(EXIT_FAILURE);
            }
            buff_up[buff_index] = '"';
            ++buff_index;

            /* End of packet serialization */ //packet结束
            buff_up[buff_index] = '}'; //倒数第三层的}；且{"jver":*,...,"data":""}为一个packet
            ++buff_index;
            ++pkt_in_dgram; //{"rxpk":[{},...,{}]}，每个{}是一个packet

            //记录接收
            if (p->modulation == MOD_LORA) { //LoRa调制
                /* Log nb of packets per channel, per SF */
                nb_pkt_log[p->if_chain][p->datarate - 5] += 1; //SF:5~12，所以(SF-5):0~7
                nb_pkt_received_lora += 1;

                /* Log nb of packets for ref_payload (DEBUG) */ //Total number of LoRa packet received
                for (k = 0; k < debugconf.nb_ref_payload; k++) {
                    if ((p->payload[0] == (uint8_t)(debugconf.ref_payload[k].id >> 24)) &&
                        (p->payload[1] == (uint8_t)(debugconf.ref_payload[k].id >> 16)) &&
                        (p->payload[2] == (uint8_t)(debugconf.ref_payload[k].id >> 8))  &&
                        (p->payload[3] == (uint8_t)(debugconf.ref_payload[k].id >> 0))) {
                            nb_pkt_received_ref[k] += 1;
                        }
                }
            } else if (p->modulation == MOD_FSK) { //FSK调制
                nb_pkt_log[p->if_chain][0] += 1; //看作在Concentrator "IF" channel    = if_chain且SF=5时接收到
                nb_pkt_received_fsk += 1;
            }
        }


        /* DEBUG: print the number of packets received per channel and per SF */ //仅用于DEBUG，显示上面记录的接收
        {
            int l, m;
            MSG_PRINTF(DEBUG_PKT_FWD, "\n");
            for (l = 0; l < (LGW_IF_CHAIN_NB - 1); l++) { //if chain: 0~8, sf: 5~12
                MSG_PRINTF(DEBUG_PKT_FWD, "CH%d: ", l);
                for (m = 0; m < 8; m++) {
                    MSG_PRINTF(DEBUG_PKT_FWD, "\t%d", nb_pkt_log[l][m]);
                }
                MSG_PRINTF(DEBUG_PKT_FWD, "\n");
            }
            MSG_PRINTF(DEBUG_PKT_FWD, "FSK: \t%d", nb_pkt_log[9][0]); ////if chain "FSK channel": 9, sf:5
            MSG_PRINTF(DEBUG_PKT_FWD, "\n");
            MSG_PRINTF(DEBUG_PKT_FWD, "Total number of LoRa packet received: %u\n", nb_pkt_received_lora);
            MSG_PRINTF(DEBUG_PKT_FWD, "Total number of FSK packet received: %u\n", nb_pkt_received_fsk);
            for (l = 0; l < debugconf.nb_ref_payload; l++) {
                MSG_PRINTF(DEBUG_PKT_FWD, "Total number of LoRa packet received from 0x%08X: %u\n", debugconf.ref_payload[l].id, nb_pkt_received_ref[l]);
            }
        }

        /* restart fetch sequence without sending empty JSON if all packets have been filtered out */  //判断是否还有数据包
        if (pkt_in_dgram == 0) { //所有packet都没有通过CRC校验
            if (send_report == true) { //只发"stat"
                /* need to clean up the beginning of the payload */
                buff_index -= 8; /* removes "rxpk":[ */
            } else { //什么都不发
                /* all packet have been filtered out and no report, restart loop */
                continue; //退出大循环：按停止键那个
            }
        } else { //有packet的时候只发 "rxpk"
            /* end of packet array */
            buff_up[buff_index] = ']'; //倒数第三层的｝后加一个倒数第二层的]
            ++buff_index;
            /* add separator if needed */
            if (send_report == true) { //有packet的时候既发"rxpk"又发"stat"
                buff_up[buff_index] = ','; //倒数第三层的}后加一个,
                ++buff_index;
            }
        }

        /* add status report if a new one is available */ //status report："stat" object，添加到buff_up中
        if (send_report == true) {
            pthread_mutex_lock(&mx_stat_rep);
            report_ready = false; //将report_ready改为false
            //再将"stat":...添加到buff_up中
            j = snprintf((char *)(buff_up + buff_index), TX_BUFF_SIZE-buff_index, "%s", status_report);
            pthread_mutex_unlock(&mx_stat_rep);
            if (j > 0) { //snprintf执行成功
                buff_index += j;
            } else {
                MSG("ERROR: [up] snprintf failed line %u\n", (__LINE__ - 5));
                exit(EXIT_FAILURE);
            }
        }

        /* end of JSON datagram payload */ //datagram结束
        buff_up[buff_index] = '}'; //倒数第一层的}
        ++buff_index;
        buff_up[buff_index] = 0; /* add string terminator, for safety */

        printf("\nJSON up: %s\n", (char *)(buff_up + 12)); /* DEBUG: display JSON payload */

        /* send datagram to server */ //发送上行datagrams
        send(sock_up, (void *)buff_up, buff_index, 0); //socket send
        clock_gettime(CLOCK_MONOTONIC, &send_time); //得到发送时间
        pthread_mutex_lock(&mx_meas_up);
        meas_up_dgram_sent += 1; //PUSH_DATA datagrams sent
        meas_up_network_byte += buff_index; //PUSH_DATA datagrams sent size

        /* wait for acknowledge (in 2 times, to catch extra packets) */ //PUSH_ACK packet
        for (i=0; i<2; ++i) { //两遍内
            j = recv(sock_up, (void *)buff_ack, sizeof buff_ack, 0);
            clock_gettime(CLOCK_MONOTONIC, &recv_time); //得到接收时间
            if (j == -1) { //没收到任何回复
                if (errno == EAGAIN) { /* timeout */ //暂时不可用，等第二遍
                    continue;
                } else { /* server connection error */ //不等了直接退出
                    break;
                }
            } else if ((j < 4) || (buff_ack[0] != PROTOCOL_VERSION) || (buff_ack[3] != PKT_PUSH_ACK)) { //根本不符合PUSH_ACK的结构
                //MSG("WARNING: [up] ignored invalid non-ACL packet\n");
                continue;
            } else if ((buff_ack[1] != token_h) || (buff_ack[2] != token_l)) { //token不符，不是要的PUSH_ACK
                //MSG("WARNING: [up] ignored out-of sync ACK packet\n");
                continue;
            } else {
                MSG("INFO: [up] PUSH_ACK received in %i ms\n", (int)(1000 * difftimespec(recv_time, send_time)));
                meas_up_ack_rcv += 1; //确认
                break; //不进行第二遍
            }
        }
        pthread_mutex_unlock(&mx_meas_up);
    }
    MSG("\nINFO: End of upstream thread\n");
}

/* -------------------------------------------------------------------------- */
/* --- THREAD 2: POLLING SERVER AND ENQUEUING PACKETS IN JIT QUEUE ---------- */

static int get_tx_gain_lut_index(uint8_t rf_chain, int8_t rf_power, uint8_t * lut_index) { //thread_down() prase json item "powe"：TX output power in dBm (unsigned integer, dBm precision)
    uint8_t pow_index;
    int current_best_index = -1;
    uint8_t current_best_match = 0xFF;
    int diff;

    /* Check input parameters */
    if (lut_index == NULL) {
        MSG("ERROR: %s - wrong parameter\n", __FUNCTION__);
        return -1;
    }

    /* Search requested power in TX gain LUT */
    for (pow_index = 0; pow_index < txlut[rf_chain].size; pow_index++) {
        diff = rf_power - txlut[rf_chain].lut[pow_index].rf_power;
        if (diff < 0) {
            /* The selected power must be lower or equal to requested one */
            continue;
        } else {
            /* Record the index corresponding to the closest rf_power available in LUT */
            if ((current_best_index == -1) || (diff < current_best_match)) {
                current_best_match = diff;
                current_best_index = pow_index;
            }
        }
    }

    /* Return corresponding index */
    if (current_best_index > -1) {
        *lut_index = (uint8_t)current_best_index;
    } else {
        *lut_index = 0;
        MSG("ERROR: %s - failed to find tx gain lut index\n", __FUNCTION__);
        return -1;
    }

    return 0;
}

void thread_down(void) {
    int i; /* loop variables */

    /* configuration and metadata for an outbound packet */
    struct lgw_pkt_tx_s txpkt;
    bool sent_immediate = false; /* option to sent the packet immediately */ //默认为否

    /* local timekeeping variables */
    struct timespec send_time; /* time of the pull request */
    struct timespec recv_time; /* time of return from recv socket call */

    /* data buffers */
    uint8_t buff_down[1000]; /* buffer to receive downstream packets */
    uint8_t buff_req[12]; /* buffer to compose pull requests */
    int msg_len;

    /* protocol variables */
    uint8_t token_h; /* random token for acknowledgement matching */ //PULL_ACK/PULL_RESP
    uint8_t token_l; /* random token for acknowledgement matching */ //PULL_DATA
    bool req_ack = false; /* keep track of whether PULL_DATA was acknowledged or not */

    /* JSON parsing variables */
    JSON_Value *root_val = NULL;
    JSON_Object *txpk_obj = NULL;
    JSON_Value *val = NULL; /* needed to detect the absence of some fields */
    const char *str; /* pointer to sub-strings in the JSON data */
    short x0, x1;
    uint64_t x2;
    double x3, x4;

    /* variables to send on GPS timestamp */
    struct tref local_ref; /* time reference used for GPS <-> timestamp conversion */
    struct timespec gps_tx; /* GPS time that needs to be converted to timestamp */

    /* beacon variables */
    struct lgw_pkt_tx_s beacon_pkt;
    uint8_t beacon_chan;
    uint8_t beacon_loop;
    size_t beacon_RFU1_size = 0;
    size_t beacon_RFU2_size = 0;
    uint8_t beacon_pyld_idx = 0;
    time_t diff_beacon_time;
    struct timespec next_beacon_gps_time; /* gps time of next beacon packet */
    struct timespec last_beacon_gps_time; /* gps time of last enqueued beacon packet */
    int retry;

    /* beacon data fields, byte 0 is Least Significant Byte */
    int32_t field_latitude; /* 3 bytes, derived from reference latitude */
    int32_t field_longitude; /* 3 bytes, derived from reference longitude */
    uint16_t field_crc1, field_crc2;

    /* auto-quit variable */
    uint32_t autoquit_cnt = 0; /* count the number of PULL_DATA sent since the latest PULL_ACK */

    /* Just In Time downlink */
    uint32_t current_concentrator_time; //用于jit_enqueue的时间戳
    enum jit_error_e jit_result = JIT_ERROR_OK;
    enum jit_pkt_type_e downlink_type;
    enum jit_error_e warning_result = JIT_ERROR_OK;
    int32_t warning_value = 0;
    uint8_t tx_lut_idx = 0;

    /* set downstream socket RX timeout */
    i = setsockopt(sock_down, SOL_SOCKET, SO_RCVTIMEO, (void *)&pull_timeout, sizeof pull_timeout);
    if (i != 0) {
        MSG("ERROR: [down] setsockopt returned %s\n", strerror(errno));
        exit(EXIT_FAILURE);
    }

    /* pre-fill the pull request buffer with fixed fields */ //PULL_DATA packet
    buff_req[0] = PROTOCOL_VERSION; //protocol version = 2
    buff_req[3] = PKT_PULL_DATA; //PULL_DATA identifier 0x02
    *(uint32_t *)(buff_req + 4) = net_mac_h; //Gateway unique identifier (MAC address)
    *(uint32_t *)(buff_req + 8) = net_mac_l;

    /* beacon variables initialization */ //beacon信标
    last_beacon_gps_time.tv_sec = 0; //秒
    last_beacon_gps_time.tv_nsec = 0; //毫秒

    /* beacon packet parameters */
    beacon_pkt.tx_mode = ON_GPS; /* send on PPS pulse */
    beacon_pkt.rf_chain = 0; /* antenna A */
    beacon_pkt.rf_power = beacon_power;
    beacon_pkt.modulation = MOD_LORA;
    switch (beacon_bw_hz) {
        case 125000:
            beacon_pkt.bandwidth = BW_125KHZ;
            break;
        case 500000:
            beacon_pkt.bandwidth = BW_500KHZ;
            break;
        default:
            /* should not happen */
            MSG("ERROR: unsupported bandwidth for beacon\n");
            exit(EXIT_FAILURE);
    }
    switch (beacon_datarate) {
        case 8:
            beacon_pkt.datarate = DR_LORA_SF8;
            beacon_RFU1_size = 1;
            beacon_RFU2_size = 3;
            break;
        case 9:
            beacon_pkt.datarate = DR_LORA_SF9;
            beacon_RFU1_size = 2;
            beacon_RFU2_size = 0;
            break;
        case 10:
            beacon_pkt.datarate = DR_LORA_SF10;
            beacon_RFU1_size = 3;
            beacon_RFU2_size = 1;
            break;
        case 12:
            beacon_pkt.datarate = DR_LORA_SF12;
            beacon_RFU1_size = 5;
            beacon_RFU2_size = 3;
            break;
        default:
            /* should not happen */
            MSG("ERROR: unsupported datarate for beacon\n");
            exit(EXIT_FAILURE);
    }
    beacon_pkt.size = beacon_RFU1_size + 4 + 2 + 7 + beacon_RFU2_size + 2;
    beacon_pkt.coderate = CR_LORA_4_5;
    beacon_pkt.invert_pol = false;
    beacon_pkt.preamble = 10;
    beacon_pkt.no_crc = true;
    beacon_pkt.no_header = true;

    /* network common part beacon fields (little endian) */
    for (i = 0; i < (int)beacon_RFU1_size; i++) {
        beacon_pkt.payload[beacon_pyld_idx++] = 0x0;
    }

    /* network common part beacon fields (little endian) */
    beacon_pyld_idx += 4; /* time (variable), filled later */
    beacon_pyld_idx += 2; /* crc1 (variable), filled later */

    /* calculate the latitude and longitude that must be publicly reported */
    field_latitude = (int32_t)((reference_coord.lat / 90.0) * (double)(1<<23));
    if (field_latitude > (int32_t)0x007FFFFF) {
        field_latitude = (int32_t)0x007FFFFF; /* +90 N is represented as 89.99999 N */
    } else if (field_latitude < (int32_t)0xFF800000) {
        field_latitude = (int32_t)0xFF800000;
    }
    field_longitude = (int32_t)((reference_coord.lon / 180.0) * (double)(1<<23));
    if (field_longitude > (int32_t)0x007FFFFF) {
        field_longitude = (int32_t)0x007FFFFF; /* +180 E is represented as 179.99999 E */
    } else if (field_longitude < (int32_t)0xFF800000) {
        field_longitude = (int32_t)0xFF800000;
    }

    /* gateway specific beacon fields */
    beacon_pkt.payload[beacon_pyld_idx++] = beacon_infodesc;
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF &  field_latitude;
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (field_latitude >>  8);
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (field_latitude >> 16);
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF &  field_longitude;
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (field_longitude >>  8);
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (field_longitude >> 16);

    /* RFU */
    for (i = 0; i < (int)beacon_RFU2_size; i++) {
        beacon_pkt.payload[beacon_pyld_idx++] = 0x0;
    }

    /* CRC of the beacon gateway specific part fields */
    field_crc2 = crc16((beacon_pkt.payload + 6 + beacon_RFU1_size), 7 + beacon_RFU2_size);
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF &  field_crc2;
    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (field_crc2 >> 8);

    /* JIT queue initialization */
    jit_queue_init(&jit_queue[0]);
    jit_queue_init(&jit_queue[1]);

    while (!exit_sig && !quit_sig) { //未收到退出信号

        /* auto-quit if the threshold is crossed */ //自动退出
        if ((autoquit_threshold > 0) && (autoquit_cnt >= autoquit_threshold)) {
            exit_sig = true;
            MSG("INFO: [down] the last %u PULL_DATA were not ACKed, exiting application\n", autoquit_threshold);
            break;
        }

        /* generate random token for request */
        token_h = (uint8_t)rand(); /* random token */ //random token
        token_l = (uint8_t)rand(); /* random token */
        buff_req[1] = token_h;
        buff_req[2] = token_l;

        /* send PULL request and record time */ //PULL_DATA packet
        send(sock_down, (void *)buff_req, sizeof buff_req, 0);
        clock_gettime(CLOCK_MONOTONIC, &send_time); //PULL_DATA发送时间
        pthread_mutex_lock(&mx_meas_dw);
        meas_dw_pull_sent += 1;
        pthread_mutex_unlock(&mx_meas_dw);
        req_ack = false;
        autoquit_cnt++;

        /* listen to packets and process them until a new PULL request must be sent */ //即下一个PULL_DATA，Every N seconds (keepalive time)
        recv_time = send_time;
        while (((int)difftimespec(recv_time, send_time) < keepalive_time) && !exit_sig && !quit_sig) { //time interval for downstream keep-alive packet

            /* try to receive a datagram */ //receive PULL_ACK/PULL_RESP packet
            msg_len = recv(sock_down, (void *)buff_down, (sizeof buff_down)-1, 0);
            clock_gettime(CLOCK_MONOTONIC, &recv_time); //得到datagram接收时间

            /* Pre-allocate beacon slots in JiT queue, to check downlink collisions */
            beacon_loop = JIT_NUM_BEACON_IN_QUEUE - jit_queue[0].num_beacon;
            retry = 0;
            while (beacon_loop && (beacon_period != 0)) { //本机prase json之后beacon_period = 0
                pthread_mutex_lock(&mx_timeref);
                /* Wait for GPS to be ready before inserting beacons in JiT queue */ //需开启gps reference
                if ((gps_ref_valid == true) && (xtal_correct_ok == true)) {

                    /* compute GPS time for next beacon to come      */
                    /*   LoRaWAN: T = k*beacon_period + TBeaconDelay */
                    /*            with TBeaconDelay = [1.5ms +/- 1µs]*/
                    if (last_beacon_gps_time.tv_sec == 0) {
                        /* if no beacon has been queued, get next slot from current GPS time */
                        diff_beacon_time = time_reference_gps.gps.tv_sec % ((time_t)beacon_period);
                        next_beacon_gps_time.tv_sec = time_reference_gps.gps.tv_sec +
                                                        ((time_t)beacon_period - diff_beacon_time);
                    } else {
                        /* if there is already a beacon, take it as reference */
                        next_beacon_gps_time.tv_sec = last_beacon_gps_time.tv_sec + beacon_period;
                    }
                    /* now we can add a beacon_period to the reference to get next beacon GPS time */
                    next_beacon_gps_time.tv_sec += (retry * beacon_period);
                    next_beacon_gps_time.tv_nsec = 0;

#if DEBUG_BEACON //我认为，这种方法可以将测试代码加进来。当需要开启测试的时候，只要将常量变1就好了。而不要测试的时候，只要将常量变0
                    {
                    time_t time_unix; //UNIX纪元

                    time_unix = time_reference_gps.gps.tv_sec + UNIX_GPS_EPOCH_OFFSET; //UNIX->GPS
                    MSG_DEBUG(DEBUG_BEACON, "GPS-now : %s", ctime(&time_unix));
                    time_unix = last_beacon_gps_time.tv_sec + UNIX_GPS_EPOCH_OFFSET;
                    MSG_DEBUG(DEBUG_BEACON, "GPS-last: %s", ctime(&time_unix));
                    time_unix = next_beacon_gps_time.tv_sec + UNIX_GPS_EPOCH_OFFSET;
                    MSG_DEBUG(DEBUG_BEACON, "GPS-next: %s", ctime(&time_unix));
                    }
#endif

                    /* convert GPS time to concentrator time, and set packet counter for JiT trigger */
                    lgw_gps2cnt(time_reference_gps, next_beacon_gps_time, &(beacon_pkt.count_us));
                    pthread_mutex_unlock(&mx_timeref);

                    /* apply frequency correction to beacon TX frequency */
                    if (beacon_freq_nb > 1) {
                        beacon_chan = (next_beacon_gps_time.tv_sec / beacon_period) % beacon_freq_nb; /* floor rounding */
                    } else {
                        beacon_chan = 0;
                    }
                    /* Compute beacon frequency */
                    beacon_pkt.freq_hz = beacon_freq_hz + (beacon_chan * beacon_freq_step);

                    /* load time in beacon payload */
                    beacon_pyld_idx = beacon_RFU1_size;
                    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF &  next_beacon_gps_time.tv_sec;
                    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (next_beacon_gps_time.tv_sec >>  8);
                    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (next_beacon_gps_time.tv_sec >> 16);
                    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (next_beacon_gps_time.tv_sec >> 24);

                    /* calculate CRC */
                    field_crc1 = crc16(beacon_pkt.payload, 4 + beacon_RFU1_size); /* CRC for the network common part */
                    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & field_crc1;
                    beacon_pkt.payload[beacon_pyld_idx++] = 0xFF & (field_crc1 >> 8);

                    /* Insert beacon packet in JiT queue */ //TX scheduling，插入beacon到jit
                    pthread_mutex_lock(&mx_concent);
                    lgw_get_instcnt(&current_concentrator_time);
                    pthread_mutex_unlock(&mx_concent);
					
					//jit_result是错误类型
                    jit_result = jit_enqueue(&jit_queue[0], current_concentrator_time, &beacon_pkt, JIT_PKT_TYPE_BEACON);
                    if (jit_result == JIT_ERROR_OK) {
                        /* update stats */
                        pthread_mutex_lock(&mx_meas_dw);
                        meas_nb_beacon_queued += 1;
                        pthread_mutex_unlock(&mx_meas_dw);

                        /* One more beacon in the queue */
                        beacon_loop--; //新信标进入jit队列后剩余容量变小，依靠这个结束最内层循环
                        retry = 0;
                        last_beacon_gps_time.tv_sec = next_beacon_gps_time.tv_sec; /* keep this beacon time as reference for next one to be programmed */

                        /* display beacon payload */
                        MSG("INFO: Beacon queued (count_us=%u, freq_hz=%u, size=%u):\n", beacon_pkt.count_us, beacon_pkt.freq_hz, beacon_pkt.size);
                        printf( "   => " );
                        for (i = 0; i < beacon_pkt.size; ++i) {
                            MSG("%02X ", beacon_pkt.payload[i]);
                        }
                        MSG("\n");
                    } else {
                        MSG_DEBUG(DEBUG_BEACON, "--> beacon queuing failed with %d\n", jit_result);
                        /* update stats */
                        pthread_mutex_lock(&mx_meas_dw);
                        if (jit_result != JIT_ERROR_COLLISION_BEACON) { //只有这一种错误得到赦免
                            meas_nb_beacon_rejected += 1;
                        }
                        pthread_mutex_unlock(&mx_meas_dw);
                        /* In case previous enqueue failed, we retry one period later until it succeeds */
                        /* Note: In case the GPS has been unlocked for a while, there can be lots of retries */
                        /*       to be done from last beacon time to a new valid one */
                        retry++;
                        MSG_DEBUG(DEBUG_BEACON, "--> beacon queuing retry=%d\n", retry);
                    }
                } else {
                    pthread_mutex_unlock(&mx_timeref);
                    break;
                }
            }

			//上面是beacon进入jit
			//下面是downlink packet进入jit

            /* if no network message was received, got back to listening sock_down socket */
            if (msg_len == -1) {
                //MSG("WARNING: [down] recv returned %s\n", strerror(errno)); /* too verbose */
                continue;
            }

            /* if the datagram does not respect protocol, just ignore it */
            if ((msg_len < 4) || (buff_down[0] != PROTOCOL_VERSION) || ((buff_down[3] != PKT_PULL_RESP) && (buff_down[3] != PKT_PULL_ACK))) { //PULL_ACK packet or PULL_RESP packet
                MSG("WARNING: [down] ignoring invalid packet len=%d, protocol_version=%d, id=%d\n",
                        msg_len, buff_down[0], buff_down[3]);
                continue;
            }

            /* if the datagram is an ACK, check token */ //PULL_ACK packet
            if (buff_down[3] == PKT_PULL_ACK) {
                if ((buff_down[1] == token_h) && (buff_down[2] == token_l)) {
                    if (req_ack) { //之前已经收到过PULL_ACK了
                        MSG("INFO: [down] duplicate ACK received :)\n");
                    } else { /* if that packet was not already acknowledged */
                        req_ack = true;
                        autoquit_cnt = 0;
                        pthread_mutex_lock(&mx_meas_dw);
                        meas_dw_ack_rcv += 1;
                        pthread_mutex_unlock(&mx_meas_dw);
                        MSG("INFO: [down] PULL_ACK received in %i ms\n", (int)(1000 * difftimespec(recv_time, send_time)));
                    }
                } else { /* out-of-sync token */
                    MSG("INFO: [down] received out-of-sync ACK\n"); //token不对
                }
                continue; //结束这一轮循环，不再继续运行
            }

            /* the datagram is a PULL_RESP */ //PULL_RESP packet
            buff_down[msg_len] = 0; /* add string terminator, just to be safe */
            MSG("INFO: [down] PULL_RESP received  - token[%d:%d] :)\n", buff_down[1], buff_down[2]); /* very verbose */ //verbose：冗长
            printf("\nJSON down: %s\n", (char *)(buff_down + 4)); /* DEBUG: display JSON payload */

            /* initialize TX struct and try to parse JSON */ //解析json结构
            memset(&txpkt, 0, sizeof txpkt);
            root_val = json_parse_string_with_comments((const char *)(buff_down + 4)); /* JSON offset */
            if (root_val == NULL) {
                MSG("WARNING: [down] invalid JSON, TX aborted\n");
                continue; //结束这一轮循环，不再继续运行
            }

            /* look for JSON sub-object 'txpk' */ //Downstream JSON data structure: The root object of PULL_RESP packet must contain an object named "txpk"
            txpk_obj = json_object_get_object(json_value_get_object(root_val), "txpk");
            if (txpk_obj == NULL) {
                MSG("WARNING: [down] no \"txpk\" object in JSON, TX aborted\n");
                json_value_free(root_val);
                continue;
            }

            /* Parse "immediate" tag, or target timestamp, or UTC time to be converted by GPS (mandatory) */  //解析txpk中前三个“immediate、tmst或tmms”以确定什么时候发送数据包
            i = json_object_get_boolean(txpk_obj,"imme"); /* can be 1 if true, 0 if false, or -1 if not a JSON boolean */
            if (i == 1) {
                /* TX procedure: send immediately */
                sent_immediate = true;
                downlink_type = JIT_PKT_TYPE_DOWNLINK_CLASS_C; //下行链路C类型，一直能够接收
                MSG("INFO: [down] a packet will be sent in \"immediate\" mode\n");
            } else { //不是imme但是tmst
                sent_immediate = false;
                val = json_object_get_value(txpk_obj,"tmst");
                if (val != NULL) {
                    /* TX procedure: send on timestamp value */
				    //ClassA的txpkt.count_us直接prase得到
                    txpkt.count_us = (uint32_t)json_value_get_number(val);

                    /* Concentrator timestamp is given, we consider it is a Class A downlink */
                    downlink_type = JIT_PKT_TYPE_DOWNLINK_CLASS_A; //下行链路A类型
                } else { //既不是imme也不是tmst，只能是tmms
                    /* TX procedure: send on GPS time (converted to timestamp value) */
                    val = json_object_get_value(txpk_obj, "tmms");
                    if (val == NULL) {
                        MSG("WARNING: [down] no mandatory \"txpk.tmst\" or \"txpk.tmms\" objects in JSON, TX aborted\n");
                        json_value_free(root_val);
                        continue; //跳过
                    }
                    if (gps_enabled == true) { //CLassB必须要开启GPS
                        pthread_mutex_lock(&mx_timeref);
                        if (gps_ref_valid == true) {
                            local_ref = time_reference_gps; //获得时间转换参考
                            pthread_mutex_unlock(&mx_timeref);
                        } else {
                            pthread_mutex_unlock(&mx_timeref);
                            MSG("WARNING: [down] no valid GPS time reference yet, impossible to send packet on specific GPS time, TX aborted\n");
                            json_value_free(root_val);

                            /* send acknoledge datagram to server */
                            send_tx_ack(buff_down[1], buff_down[2], JIT_ERROR_GPS_UNLOCKED, 0);
                            continue;
                        }
                    } else {
                        MSG("WARNING: [down] GPS disabled, impossible to send packet on specific GPS time, TX aborted\n");
                        json_value_free(root_val);

                        /* send acknoledge datagram to server */ //GPS_UNLOCKED
                        send_tx_ack(buff_down[1], buff_down[2], JIT_ERROR_GPS_UNLOCKED, 0);
                        continue; //跳过
                    }

                    /* Get GPS time from JSON */
                    x2 = (uint64_t)json_value_get_number(val); //得到"tmms"的数值

                    /* Convert GPS time from milliseconds to timespec */ //gps_tx为structure timespec
                    x3 = modf((double)x2/1E3, &x4); //x4为整数部分，x3为小数部分
                    gps_tx.tv_sec = (time_t)x4; /* get seconds from integer part */
                    gps_tx.tv_nsec = (long)(x3 * 1E9); /* get nanoseconds from fractional part */

                    /* transform GPS time to timestamp */
					//There are 2 cases for which we need to convert a GPS time to concentrator counter: - Class B downlink
                    //gps_tx -> txpkt.count_us
					i = lgw_gps2cnt(local_ref, gps_tx, &(txpkt.count_us));
                    if (i != LGW_GPS_SUCCESS) {
                        MSG("WARNING: [down] could not convert GPS time to timestamp, TX aborted\n");
                        json_value_free(root_val);
                        continue;
                    } else {
                        MSG("INFO: [down] a packet will be sent on timestamp value %u (calculated from GPS time)\n", txpkt.count_us);
                    }

                    /* GPS timestamp is given, we consider it is a Class B downlink */
                    downlink_type = JIT_PKT_TYPE_DOWNLINK_CLASS_B;
                }
            }

            /* Parse "No CRC" flag (optional field) */
            val = json_object_get_value(txpk_obj,"ncrc");
            if (val != NULL) {
                txpkt.no_crc = (bool)json_value_get_boolean(val);
            }

            /* Parse "No header" flag (optional field) */
            val = json_object_get_value(txpk_obj,"nhdr");
            if (val != NULL) {
                txpkt.no_header = (bool)json_value_get_boolean(val);
            }

            /* parse target frequency (mandatory) */
            val = json_object_get_value(txpk_obj,"freq");
            if (val == NULL) {
                MSG("WARNING: [down] no mandatory \"txpk.freq\" object in JSON, TX aborted\n");
                json_value_free(root_val);
                continue;
            }
            txpkt.freq_hz = (uint32_t)((double)(1.0e6) * json_value_get_number(val));

            /* parse RF chain used for TX (mandatory) */
            val = json_object_get_value(txpk_obj,"rfch");
            if (val == NULL) {
                MSG("WARNING: [down] no mandatory \"txpk.rfch\" object in JSON, TX aborted\n");
                json_value_free(root_val);
                continue;
            }
            txpkt.rf_chain = (uint8_t)json_value_get_number(val);
            if (tx_enable[txpkt.rf_chain] == false) {
                MSG("WARNING: [down] TX is not enabled on RF chain %u, TX aborted\n", txpkt.rf_chain);
                json_value_free(root_val);
                continue;
            }

            /* parse TX power (optional field) */
            val = json_object_get_value(txpk_obj,"powe");
            if (val != NULL) {
                txpkt.rf_power = (int8_t)json_value_get_number(val) - antenna_gain;
            }

            /* Parse modulation (mandatory) */
            str = json_object_get_string(txpk_obj, "modu");
            if (str == NULL) {
                MSG("WARNING: [down] no mandatory \"txpk.modu\" object in JSON, TX aborted\n");
                json_value_free(root_val);
                continue;
            }
            if (strcmp(str, "LORA") == 0) { //LoRa调制
                /* Lora modulation */
                txpkt.modulation = MOD_LORA;

                /* Parse Lora spreading-factor and modulation bandwidth (mandatory) */
                str = json_object_get_string(txpk_obj, "datr");
                if (str == NULL) {
                    MSG("WARNING: [down] no mandatory \"txpk.datr\" object in JSON, TX aborted\n");
                    json_value_free(root_val);
                    continue;
                }
                i = sscanf(str, "SF%2hdBW%3hd", &x0, &x1);
                if (i != 2) {
                    MSG("WARNING: [down] format error in \"txpk.datr\", TX aborted\n");
                    json_value_free(root_val);
                    continue;
                }
                switch (x0) {
                    case  5: txpkt.datarate = DR_LORA_SF5;  break;
                    case  6: txpkt.datarate = DR_LORA_SF6;  break;
                    case  7: txpkt.datarate = DR_LORA_SF7;  break;
                    case  8: txpkt.datarate = DR_LORA_SF8;  break;
                    case  9: txpkt.datarate = DR_LORA_SF9;  break;
                    case 10: txpkt.datarate = DR_LORA_SF10; break;
                    case 11: txpkt.datarate = DR_LORA_SF11; break;
                    case 12: txpkt.datarate = DR_LORA_SF12; break;
                    default:
                        MSG("WARNING: [down] format error in \"txpk.datr\", invalid SF, TX aborted\n");
                        json_value_free(root_val);
                        continue;
                }
                switch (x1) {
                    case 125: txpkt.bandwidth = BW_125KHZ; break;
                    case 250: txpkt.bandwidth = BW_250KHZ; break;
                    case 500: txpkt.bandwidth = BW_500KHZ; break;
                    default:
                        MSG("WARNING: [down] format error in \"txpk.datr\", invalid BW, TX aborted\n");
                        json_value_free(root_val);
                        continue;
                }

                /* Parse ECC coding rate (optional field) */
                str = json_object_get_string(txpk_obj, "codr");
                if (str == NULL) {
                    MSG("WARNING: [down] no mandatory \"txpk.codr\" object in json, TX aborted\n");
                    json_value_free(root_val);
                    continue;
                }
                if      (strcmp(str, "4/5") == 0) txpkt.coderate = CR_LORA_4_5;
                else if (strcmp(str, "4/6") == 0) txpkt.coderate = CR_LORA_4_6;
                else if (strcmp(str, "2/3") == 0) txpkt.coderate = CR_LORA_4_6;
                else if (strcmp(str, "4/7") == 0) txpkt.coderate = CR_LORA_4_7;
                else if (strcmp(str, "4/8") == 0) txpkt.coderate = CR_LORA_4_8;
                else if (strcmp(str, "1/2") == 0) txpkt.coderate = CR_LORA_4_8;
                else {
                    MSG("WARNING: [down] format error in \"txpk.codr\", TX aborted\n");
                    json_value_free(root_val);
                    continue;
                }

                /* Parse signal polarity switch (optional field) */
                val = json_object_get_value(txpk_obj,"ipol");
                if (val != NULL) {
                    txpkt.invert_pol = (bool)json_value_get_boolean(val);
                }

                /* parse Lora preamble length (optional field, optimum min value enforced) */
                val = json_object_get_value(txpk_obj,"prea");
                if (val != NULL) {
                    i = (int)json_value_get_number(val);
                    if (i >= MIN_LORA_PREAMB) {
                        txpkt.preamble = (uint16_t)i;
                    } else {
                        txpkt.preamble = (uint16_t)MIN_LORA_PREAMB;
                    }
                } else {
                    txpkt.preamble = (uint16_t)STD_LORA_PREAMB;
                }

            } else if (strcmp(str, "FSK") == 0) { //FSK调制
                /* FSK modulation */
                txpkt.modulation = MOD_FSK;

                /* parse FSK bitrate (mandatory) */
                val = json_object_get_value(txpk_obj,"datr");
                if (val == NULL) {
                    MSG("WARNING: [down] no mandatory \"txpk.datr\" object in JSON, TX aborted\n");
                    json_value_free(root_val);
                    continue;
                }
                txpkt.datarate = (uint32_t)(json_value_get_number(val));

                /* parse frequency deviation (mandatory) */ //只有FSK有发射频率偏移
                val = json_object_get_value(txpk_obj,"fdev");
                if (val == NULL) {
                    MSG("WARNING: [down] no mandatory \"txpk.fdev\" object in JSON, TX aborted\n");
                    json_value_free(root_val);
                    continue;
                }
                txpkt.f_dev = (uint8_t)(json_value_get_number(val) / 1000.0); /* JSON value in Hz, txpkt.f_dev in kHz */

                /* parse FSK preamble length (optional field, optimum min value enforced) */
                val = json_object_get_value(txpk_obj,"prea");
                if (val != NULL) {
                    i = (int)json_value_get_number(val);
                    if (i >= MIN_FSK_PREAMB) {
                        txpkt.preamble = (uint16_t)i;
                    } else {
                        txpkt.preamble = (uint16_t)MIN_FSK_PREAMB;
                    }
                } else {
                    txpkt.preamble = (uint16_t)STD_FSK_PREAMB;
                }

            } else { //调制方式不合法
                MSG("WARNING: [down] invalid modulation in \"txpk.modu\", TX aborted\n");
                json_value_free(root_val);
                continue;
            }

            /* Parse payload length (mandatory) */
            val = json_object_get_value(txpk_obj,"size");
            if (val == NULL) {
                MSG("WARNING: [down] no mandatory \"txpk.size\" object in JSON, TX aborted\n");
                json_value_free(root_val);
                continue;
            }
            txpkt.size = (uint16_t)json_value_get_number(val);

            /* Parse payload data (mandatory) */
            str = json_object_get_string(txpk_obj, "data");
            if (str == NULL) {
                MSG("WARNING: [down] no mandatory \"txpk.data\" object in JSON, TX aborted\n");
                json_value_free(root_val);
                continue;
            }
			//txpkt->payload使用base64解密
            i = b64_to_bin(str, strlen(str), txpkt.payload, sizeof txpkt.payload);
            if (i != txpkt.size) {
                MSG("WARNING: [down] mismatch between .size and .data size once converter to binary\n");
            }

            /* free the JSON parse tree from memory */
            json_value_free(root_val);

            /* select TX mode */
            if (sent_immediate) {
                txpkt.tx_mode = IMMEDIATE; //Class-C
            } else {
                txpkt.tx_mode = TIMESTAMPED; //Note: even if a Class-B downlink is given with a GPS timestamp, the concentrator TX mode is configured as “TIMESTAMP”, and not “ON_GPS”.
            }

            /* record measurement data */
            pthread_mutex_lock(&mx_meas_dw);
            meas_dw_dgram_rcv += 1; /* count only datagrams with no JSON errors */
            meas_dw_network_byte += msg_len; /* meas_dw_network_byte */
            meas_dw_payload_byte += txpkt.size;
            pthread_mutex_unlock(&mx_meas_dw);

            /* reset error/warning results */ //jit_result初始化为JIT_ERROR_OK
            jit_result = warning_result = JIT_ERROR_OK;
            warning_value = 0;

            /* check TX frequency before trying to queue packet */ //在插入jit前查看发射频率
            if ((txpkt.freq_hz < tx_freq_min[txpkt.rf_chain]) || (txpkt.freq_hz > tx_freq_max[txpkt.rf_chain])) {
                jit_result = JIT_ERROR_TX_FREQ;
                MSG("ERROR: Packet REJECTED, unsupported frequency - %u (min:%u,max:%u)\n", txpkt.freq_hz, tx_freq_min[txpkt.rf_chain], tx_freq_max[txpkt.rf_chain]);
            }

            /* check TX power before trying to queue packet, send a warning if not supported */ //在插入jit前查tx_gain_lut表看发射功率
            if (jit_result == JIT_ERROR_OK) {
                i = get_tx_gain_lut_index(txpkt.rf_chain, txpkt.rf_power, &tx_lut_idx);
                if ((i < 0) || (txlut[txpkt.rf_chain].lut[tx_lut_idx].rf_power != txpkt.rf_power)) {
                    /* this RF power is not supported, throw a warning, and use the closest lower power supported */
                    warning_result = JIT_ERROR_TX_POWER;
                    warning_value = (int32_t)txlut[txpkt.rf_chain].lut[tx_lut_idx].rf_power;
                    printf("WARNING: Requested TX power is not supported (%ddBm), actual power used: %ddBm\n", txpkt.rf_power, warning_value);
                    txpkt.rf_power = txlut[txpkt.rf_chain].lut[tx_lut_idx].rf_power;
                }
            }

            /* insert packet to be sent into JIT queue */ //TX scheduling，注意beacon已经在上面被插入了
            if (jit_result == JIT_ERROR_OK) { //通过了上面的check TX frequency与check TX power
                pthread_mutex_lock(&mx_concent);
                lgw_get_instcnt(&current_concentrator_time); //So at the end, it is the counter value which will be used for transmission
                pthread_mutex_unlock(&mx_concent);
                jit_result = jit_enqueue(&jit_queue[txpkt.rf_chain], current_concentrator_time, &txpkt, downlink_type); //根据downlink_type插入downlink CLASS A/B/C到JIT
                if (jit_result != JIT_ERROR_OK) { //执行jit_enqueue失败
                    printf("ERROR: Packet REJECTED (jit error=%d)\n", jit_result);
                } else {
                    /* In case of a warning having been raised before, we notify it */
                    jit_result = warning_result;
                }
                pthread_mutex_lock(&mx_meas_dw);
                meas_nb_tx_requested += 1;
                pthread_mutex_unlock(&mx_meas_dw);
            }

            /* Send acknoledge datagram to server */ //If no JSON is present (empty string), this means than no error occured
            send_tx_ack(buff_down[1], buff_down[2], jit_result, warning_value);
        }
    }
    MSG("\nINFO: End of downstream thread\n");
}

void print_tx_status(uint8_t tx_status) {
    switch (tx_status) {
        case TX_OFF:
            MSG("INFO: [jit] lgw_status returned TX_OFF\n");
            break;
        case TX_FREE:
            MSG("INFO: [jit] lgw_status returned TX_FREE\n");
            break;
        case TX_EMITTING:
            MSG("INFO: [jit] lgw_status returned TX_EMITTING\n");
            break;
        case TX_SCHEDULED:
            MSG("INFO: [jit] lgw_status returned TX_SCHEDULED\n");
            break;
        default:
            MSG("INFO: [jit] lgw_status returned UNKNOWN (%d)\n", tx_status);
            break;
    }
}


/* -------------------------------------------------------------------------- */
/* --- THREAD 3: CHECKING PACKETS TO BE SENT FROM JIT QUEUE AND SEND THEM --- */

void thread_jit(void) { //A JiT thread, which regularly checks if there is a packet in the JiT queue ready to be programmed in the concentrator, based on current concentrator internal time.
    int result = LGW_HAL_SUCCESS;
    struct lgw_pkt_tx_s pkt;
    int pkt_index = -1;
    uint32_t current_concentrator_time; //用于jit_peek的时间戳
    enum jit_error_e jit_result;
    enum jit_pkt_type_e pkt_type;
    uint8_t tx_status;
    int i;

    while (!exit_sig && !quit_sig) {
        wait_ms(10); //每10ms

        for (i = 0; i < LGW_RF_CHAIN_NB; i++) { //RF chain = jit_queue
            /* transfer data and metadata to the concentrator, and schedule TX */
            pthread_mutex_lock(&mx_concent);
            lgw_get_instcnt(&current_concentrator_time); //based on current concentrator internal time
            pthread_mutex_unlock(&mx_concent);
            jit_result = jit_peek(&jit_queue[i], current_concentrator_time, &pkt_index); //checks if the queue contains a packet that must be passed immediately to the concentrator for transmission and returns corresponding index if any.
			//检查当前是否有报文需要发送到Concentrator
			if (jit_result == JIT_ERROR_OK) { //the queue contains a packet that must be passed immediately to the concentrator for transmission and returns corresponding index if any
                        /* update beacon stats */
			    //若有
                if (pkt_index > -1) {
                    jit_result = jit_dequeue(&jit_queue[i], pkt_index, &pkt, &pkt_type); //actually removes from the queue the packet at index given by peek function
					if (jit_result == JIT_ERROR_OK) {
                        if (pkt_type == JIT_PKT_TYPE_BEACON) { //downlink packet type beacon
                            /* Compensate breacon frequency with xtal error */
                            pthread_mutex_lock(&mx_xcorr);
                            pkt.freq_hz = (uint32_t)(xtal_correct * (double)pkt.freq_hz);
                            MSG_DEBUG(DEBUG_BEACON, "beacon_pkt.freq_hz=%u (xtal_correct=%.15lf)\n", pkt.freq_hz, xtal_correct);
                            pthread_mutex_unlock(&mx_xcorr);

							//经过了peek和dequeue之后开始处理beacon与packet

                            /* Update statistics */
                            pthread_mutex_lock(&mx_meas_dw);
                            meas_nb_beacon_sent += 1;
                            pthread_mutex_unlock(&mx_meas_dw);
                            MSG("INFO: Beacon dequeued (count_us=%u)\n", pkt.count_us);
                        }

                        /* check if concentrator is free for sending new packet */ //检查Concentrator当前是否可发送
                        pthread_mutex_lock(&mx_concent); /* may have to wait for a fetch to finish */
                        result = lgw_status(pkt.rf_chain, TX_STATUS, &tx_status); //查看用于发射的rf_chain的情况
                        pthread_mutex_unlock(&mx_concent); /* free concentrator ASAP */
                        if (result == LGW_HAL_ERROR) { //lgw_status执行失败，无法获得状态
                            MSG("WARNING: [jit%d] lgw_status failed\n", i);
                        } else { //LGW_HAL_SUCCESS：获得了状态
                            if (tx_status == TX_EMITTING) {
                                MSG("ERROR: concentrator is currently emitting on rf_chain %d\n", i);
                                print_tx_status(tx_status);
                                continue;
                            } else if (tx_status == TX_SCHEDULED) {
                                MSG("WARNING: a downlink was already scheduled on rf_chain %d, overwritting it...\n", i);
                                print_tx_status(tx_status);
                            } else {
                                /* Nothing to do */
                            }
                        }

                        /* send packet to concentrator */
                        pthread_mutex_lock(&mx_concent); /* may have to wait for a fetch to finish */
                        if (spectral_scan_params.enable == true) {
                            result = lgw_spectral_scan_abort();
                            if (result != LGW_HAL_SUCCESS) {
                                MSG("WARNING: [jit%d] lgw_spectral_scan_abort failed\n", i);
                            }
                        }
                        result = lgw_send(&pkt); //发射数据包
                        pthread_mutex_unlock(&mx_concent); /* free concentrator ASAP */
                        if (result != LGW_HAL_SUCCESS) { //lgw_send执行失败，发送失败
                            pthread_mutex_lock(&mx_meas_dw);
                            meas_nb_tx_fail += 1;
                            pthread_mutex_unlock(&mx_meas_dw);
                            MSG("WARNING: [jit] lgw_send failed on rf_chain %d\n", i);
                            continue;
                        } else {
                            pthread_mutex_lock(&mx_meas_dw);
                            meas_nb_tx_ok += 1;
                            pthread_mutex_unlock(&mx_meas_dw);
                            MSG_DEBUG(DEBUG_PKT_FWD, "lgw_send done on rf_chain %d: count_us=%u\n", i, pkt.count_us);
                        }
                    } else {
                        MSG("ERROR: jit_dequeue failed on rf_chain %d with %d\n", i, jit_result);  //jit_dequeue返回JIT_ERROR_INVALID或JIT_ERROR_EMPTY
                    }
                }
            } else if (jit_result == JIT_ERROR_EMPTY) { //jit_peek返回JIT_ERROR_EMPTY
                /* Do nothing, it can happen */
            } else { //jit_peek返回JIT_ERROR_INVALID
                MSG("ERROR: jit_peek failed on rf_chain %d with %d\n", i, jit_result);
            }
        }
    }

    MSG("\nINFO: End of JIT thread\n");
}

/* -------------------------------------------------------------------------- */
/* --- THREAD 4: PARSE GPS MESSAGE AND KEEP GATEWAY IN SYNC ----------------- */

static void gps_process_sync(void) { //更新时间
    struct timespec gps_time;
    struct timespec utc;
    uint32_t trig_tstamp; /* concentrator timestamp associated with PPM pulse */ //用于lgw_gps_sync的时间戳
    int i = lgw_gps_get(&utc, &gps_time, NULL, NULL); //获得时间

    /* get GPS time for synchronization */
    if (i != LGW_GPS_SUCCESS) {
        MSG("WARNING: [gps] could not get GPS time from GPS\n");
        return;
    }

    /* get timestamp captured on PPM pulse  */
    pthread_mutex_lock(&mx_concent);
    i = lgw_get_trigcnt(&trig_tstamp); //Get concentrator count
    pthread_mutex_unlock(&mx_concent);
    if (i != LGW_HAL_SUCCESS) {
        MSG("WARNING: [gps] failed to read concentrator timestamp\n");
        return;
    }

    /* try to update time reference with the new GPS time & timestamp */
    pthread_mutex_lock(&mx_timeref);
    i = lgw_gps_sync(&time_reference_gps, trig_tstamp, utc, gps_time);
    pthread_mutex_unlock(&mx_timeref);
    if (i != LGW_GPS_SUCCESS) {
        MSG("WARNING: [gps] GPS out of sync, keeping previous time reference\n");
    }
}

static void gps_process_coords(void) { //更新地理位置
    /* position variable */
    struct coord_s coord;
    struct coord_s gpserr;
    int    i = lgw_gps_get(NULL, NULL, &coord, &gpserr); //获得地理位置

    /* update gateway coordinates */
    pthread_mutex_lock(&mx_meas_gps);
    if (i == LGW_GPS_SUCCESS) {
        gps_coord_valid = true;
        meas_gps_coord = coord;
        meas_gps_err = gpserr;
        // TODO: report other GPS statistics (typ. signal quality & integrity)
    } else {
        gps_coord_valid = false;
    }
    pthread_mutex_unlock(&mx_meas_gps);
}

void thread_gps(void) {
    /* serial variables */
    char serial_buff[128]; /* buffer to receive GPS data */
    size_t wr_idx = 0;     /* pointer to end of chars in buffer */

    /* variables for PPM pulse GPS synchronization */
    enum gps_msg latest_msg; /* keep track of latest NMEA message parsed */

    /* initialize some variables before loop */
    memset(serial_buff, 0, sizeof serial_buff);

    while (!exit_sig && !quit_sig) { //循环从 GPS 串口读取数据，并进行匹配
        size_t rd_idx = 0;
        size_t frame_end_idx = 0;

        /* blocking non-canonical read on serial port */
        ssize_t nb_char = read(gps_tty_fd, serial_buff + wr_idx, LGW_GPS_MIN_MSG_SIZE);
        if (nb_char <= 0) {
            MSG("WARNING: [gps] read() returned value %zd\n", nb_char);
            continue;
        }
        wr_idx += (size_t)nb_char;

        /*******************************************
         * Scan buffer for UBX/NMEA sync chars and * //UBX: time
         * attempt to decode frame if one is found * //NMEA: coordinate
         *******************************************/
        while (rd_idx < wr_idx) {
            size_t frame_size = 0;

            /* Scan buffer for UBX sync char */
            if (serial_buff[rd_idx] == (char)LGW_GPS_UBX_SYNC_CHAR) { //parse UBX messages (using lgw_parse_ubx) to get actual native GPS time

                /***********************
                 * Found UBX sync char *
                 ***********************/
                latest_msg = lgw_parse_ubx(&serial_buff[rd_idx], (wr_idx - rd_idx), &frame_size);

                if (frame_size > 0) {
                    if (latest_msg == INCOMPLETE) {
                        /* UBX header found but frame appears to be missing bytes */
                        frame_size = 0;
                    } else if (latest_msg == INVALID) {
                        /* message header received but message appears to be corrupted */
                        MSG("WARNING: [gps] could not get a valid message from GPS (no time)\n");
                        frame_size = 0;
                    } else if (latest_msg == UBX_NAV_TIMEGPS) {
                        gps_process_sync(); //时间信息
                    }
                }
            } else if (serial_buff[rd_idx] == (char)LGW_GPS_NMEA_SYNC_CHAR) { //parse NMEA sentences (using lgw_parse_nmea) to get location and UTC time Note: the RMC sentence gives UTC time, not native GPS time.
                /************************
                 * Found NMEA sync char *
                 ************************/
                /* scan for NMEA end marker (LF = 0x0a) */
                char* nmea_end_ptr = memchr(&serial_buff[rd_idx],(int)0x0a, (wr_idx - rd_idx));

                if(nmea_end_ptr) {
                    /* found end marker */
                    frame_size = nmea_end_ptr - &serial_buff[rd_idx] + 1;
                    latest_msg = lgw_parse_nmea(&serial_buff[rd_idx], frame_size);

                    if(latest_msg == INVALID || latest_msg == UNKNOWN) {
                        /* checksum failed */
                        frame_size = 0;
                    } else if (latest_msg == NMEA_RMC) { /* Get location from RMC frames */
                        gps_process_coords(); //位置信息
                    }
                }
            }

            if (frame_size > 0) {
                /* At this point message is a checksum verified frame
                   we're processed or ignored. Remove frame from buffer */
                rd_idx += frame_size;
                frame_end_idx = rd_idx;
            } else {
                rd_idx++;
            }
        } /* ...for(rd_idx = 0... */

        if (frame_end_idx) {
          /* Frames have been processed. Remove bytes to end of last processed frame */
          memcpy(serial_buff, &serial_buff[frame_end_idx], wr_idx - frame_end_idx);
          wr_idx -= frame_end_idx;
        } /* ...for(rd_idx = 0... */

        /* Prevent buffer overflow */
        if ((sizeof(serial_buff) - wr_idx) < LGW_GPS_MIN_MSG_SIZE) {
            memcpy(serial_buff, &serial_buff[LGW_GPS_MIN_MSG_SIZE], wr_idx - LGW_GPS_MIN_MSG_SIZE);
            wr_idx -= LGW_GPS_MIN_MSG_SIZE;
        }
    }
    MSG("\nINFO: End of GPS thread\n");
}

/* -------------------------------------------------------------------------- */
/* --- THREAD 5: CHECK TIME REFERENCE AND CALCULATE XTAL CORRECTION --------- */

void thread_valid(void) {

    /* GPS reference validation variables */
    long gps_ref_age = 0;
    bool ref_valid_local = false;
    double xtal_err_cpy;

    /* variables for XTAL correction averaging */
    unsigned init_cpt = 0;
    double init_acc = 0.0;
    double x;

    /* correction debug */
    // FILE * log_file = NULL;
    // time_t now_time;
    // char log_name[64];

    /* initialization */
    // time(&now_time);
    // strftime(log_name,sizeof log_name,"xtal_err_%Y%m%dT%H%M%SZ.csv",localtime(&now_time));
    // log_file = fopen(log_name, "w");
    // setbuf(log_file, NULL);
    // fprintf(log_file,"\"xtal_correct\",\"XERR_INIT_AVG %u XERR_FILT_COEF %u\"\n", XERR_INIT_AVG, XERR_FILT_COEF); // DEBUG

    /* main loop task */
    while (!exit_sig && !quit_sig) {
        wait_ms(1000); //每秒一次

        /* calculate when the time reference was last updated */
        pthread_mutex_lock(&mx_timeref);
        gps_ref_age = (long)difftime(time(NULL), time_reference_gps.systime); //thread_gps调用的gps_process_sync更新的reference
        //GPS时钟是否有效。系统和 GPS 时间差是否超出[0, GPS_REF_MAX_AGE]范围
		if ((gps_ref_age >= 0) && (gps_ref_age <= GPS_REF_MAX_AGE)) {
            /* time ref is ok, validate and  */ //gps基准时间合理
            gps_ref_valid = true; //validate time reference
            ref_valid_local = true;
            xtal_err_cpy = time_reference_gps.xtal_err;
            //printf("XTAL err: %.15lf (1/XTAL_err:%.15lf)\n", xtal_err_cpy, 1/xtal_err_cpy); // DEBUG
        } else {
            /* time ref is too old, invalidate */ //gps基准时间不合理
            gps_ref_valid = false; //invalidate time reference
            ref_valid_local = false;
        }
        pthread_mutex_unlock(&mx_timeref);

        /* manage XTAL correction */
        if (ref_valid_local == false) { //gps基准时间不合理
            /* couldn't sync, or sync too old -> invalidate XTAL correction */
            pthread_mutex_lock(&mx_xcorr);
            xtal_correct_ok = false; //invalidate XTAL correction
            xtal_correct = 1.0;
            pthread_mutex_unlock(&mx_xcorr);
            init_cpt = 0;
            init_acc = 0.0;
        } else { //gps基准时间合理
            if (init_cpt < XERR_INIT_AVG) {
                /* initial accumulation */
                init_acc += xtal_err_cpy;
                ++init_cpt;
            } else if (init_cpt == XERR_INIT_AVG) {
                /* initial average calculation */
                pthread_mutex_lock(&mx_xcorr);
                xtal_correct = (double)(XERR_INIT_AVG) / init_acc;
                //printf("XERR_INIT_AVG=%d, init_acc=%.15lf\n", XERR_INIT_AVG, init_acc);
                xtal_correct_ok = true; //validate XTAL correction
                pthread_mutex_unlock(&mx_xcorr);
                ++init_cpt;
                // fprintf(log_file,"%.18lf,\"average\"\n", xtal_correct); // DEBUG
            } else {
                /* tracking with low-pass filter */
                x = 1 / xtal_err_cpy;
                pthread_mutex_lock(&mx_xcorr);
                xtal_correct = xtal_correct - xtal_correct/XERR_FILT_COEF + x/XERR_FILT_COEF;
                pthread_mutex_unlock(&mx_xcorr);
                // fprintf(log_file,"%.18lf,\"track\"\n", xtal_correct); // DEBUG
            }
        }

        //printf("Time ref: %s, XTAL correct: %s (%.15lf)\n", ref_valid_local?"valid":"invalid", xtal_correct_ok?"valid":"invalid", xtal_correct); // DEBUG
    }
    MSG("\nINFO: End of validation thread\n");
}

/* -------------------------------------------------------------------------- */
/* --- THREAD 6: BACKGROUND SPECTRAL SCAN                           --------- */

void thread_spectral_scan(void) {
    int i, x;
    uint32_t freq_hz = spectral_scan_params.freq_hz_start;
    uint32_t freq_hz_stop = spectral_scan_params.freq_hz_start + spectral_scan_params.nb_chan * 200E3;
    int16_t levels[LGW_SPECTRAL_SCAN_RESULT_SIZE];
    uint16_t results[LGW_SPECTRAL_SCAN_RESULT_SIZE];
    struct timeval tm_start;
    lgw_spectral_scan_status_t status;
    uint8_t tx_status = TX_FREE;
    bool spectral_scan_started;
    bool exit_thread = false;

    /* main loop task */
    while (!exit_sig && !quit_sig) {
        /* Pace the scan thread (1 sec min), and avoid waiting several seconds when exit */
        for (i = 0; i < (int)(spectral_scan_params.pace_s ? spectral_scan_params.pace_s : 1); i++) {
            if (exit_sig || quit_sig) {
                exit_thread = true;
                break;
            }
            wait_ms(1000);
        }
        if (exit_thread == true) {
            break;
        }

        spectral_scan_started = false;

        /* Start spectral scan (if no downlink programmed) */
        pthread_mutex_lock(&mx_concent);
        /* -- Check if there is a downlink programmed */
        for (i = 0; i < LGW_RF_CHAIN_NB; i++) {
            if (tx_enable[i] == true) {
                x = lgw_status((uint8_t)i, TX_STATUS, &tx_status);
                if (x != LGW_HAL_SUCCESS) {
                    printf("ERROR: failed to get TX status on chain %d\n", i);
                } else {
                    if (tx_status == TX_SCHEDULED || tx_status == TX_EMITTING) {
                        printf("INFO: skip spectral scan (downlink programmed on RF chain %d)\n", i);
                        break; /* exit for loop */
                    }
                }
            }
        }
        if (tx_status != TX_SCHEDULED && tx_status != TX_EMITTING) {
            x = lgw_spectral_scan_start(freq_hz, spectral_scan_params.nb_scan);
            if (x != 0) {
                printf("ERROR: spectral scan start failed\n");
                pthread_mutex_unlock(&mx_concent);
                continue; /* main while loop */
            }
            spectral_scan_started = true;
        }
        pthread_mutex_unlock(&mx_concent);

        if (spectral_scan_started == true) {
            /* Wait for scan to be completed */
            status = LGW_SPECTRAL_SCAN_STATUS_UNKNOWN;
            timeout_start(&tm_start);
            do {
                /* handle timeout */
                if (timeout_check(tm_start, 2000) != 0) {
                    printf("ERROR: %s: TIMEOUT on Spectral Scan\n", __FUNCTION__);
                    break;  /* do while */
                }

                /* get spectral scan status */
                pthread_mutex_lock(&mx_concent);
                x = lgw_spectral_scan_get_status(&status);
                pthread_mutex_unlock(&mx_concent);
                if (x != 0) {
                    printf("ERROR: spectral scan status failed\n");
                    break; /* do while */
                }

                /* wait a bit before checking status again */
                wait_ms(10);
            } while (status != LGW_SPECTRAL_SCAN_STATUS_COMPLETED && status != LGW_SPECTRAL_SCAN_STATUS_ABORTED);

            if (status == LGW_SPECTRAL_SCAN_STATUS_COMPLETED) {
                /* Get spectral scan results */
                memset(levels, 0, sizeof levels);
                memset(results, 0, sizeof results);
                pthread_mutex_lock(&mx_concent);
                x = lgw_spectral_scan_get_results(levels, results);
                pthread_mutex_unlock(&mx_concent);
                if (x != 0) {
                    printf("ERROR: spectral scan get results failed\n");
                    continue; /* main while loop */
                }

                /* print results */
                printf("SPECTRAL SCAN - %u Hz: ", freq_hz);
                for (i = 0; i < LGW_SPECTRAL_SCAN_RESULT_SIZE; i++) {
                    printf("%u ", results[i]);
                }
                printf("\n");

                /* Next frequency to scan */
                freq_hz += 200000; /* 200kHz channels */
                if (freq_hz >= freq_hz_stop) {
                    freq_hz = spectral_scan_params.freq_hz_start;
                }
            } else if (status == LGW_SPECTRAL_SCAN_STATUS_ABORTED) {
                printf("INFO: %s: spectral scan has been aborted\n", __FUNCTION__);
            } else {
                printf("ERROR: %s: spectral scan status us unexpected 0x%02X\n", __FUNCTION__, status);
            }
        }
    }
    printf("\nINFO: End of Spectral Scan thread\n");
}

/* --- EOF ------------------------------------------------------------------ */
