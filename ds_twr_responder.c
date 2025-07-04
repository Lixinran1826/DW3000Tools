///*! ----------------------------------------------------------------------------
// *  @file    ds_twr_responder.c
// *  @brief   Double-sided two-way ranging (DS TWR) responder example code
// *
// *           This is a simple code example which acts as the responder in a DS TWR distance measurement exchange. This application waits for a "poll"
// *           message (recording the RX time-stamp of the poll) expected from the "DS TWR initiator" example code (companion to this application), and
// *           then sends a "response" message recording its TX time-stamp, after which it waits for a "final" message from the initiator to complete
// *           the exchange. The final message contains the remote initiator's time-stamps of poll TX, response RX and final TX. With this data and the
// *           local time-stamps, (of poll RX, response TX and final RX), this example application works out a value for the time-of-flight over-the-air
// *           and, thus, the estimated distance between the two devices, which it writes to the LCD.
// *
// * @attention
// *·                                                             
// * Copyright 2015 - 2021 (c) Decawave Ltd, Dublin, Ireland.
// *
// * All rights reserved.
// *
// * @author Decawave
// */

//#include "deca_probe_interface.h"
//#include <config_options.h>

#include <deca_device_api.h>
#include <deca_spi.h>
#include <example_selection.h>
#include <port.h>
#include <shared_defines.h>
#include <shared_functions.h>

#include <deca_regs.h>
#include <math.h>

#if defined(TEST_DS_TWR_RESPONDER)
#define ANCHOR_ID 0  // 0-trans;1-recv
#define ANCHOR_NUM 2

extern void test_run_info(unsigned char *data);
extern void UART_WriteData(uint8_t *pData, uint32_t dataLen);

/* Example application name */
#define APP_NAME "DS TWR RESP v1.0"


/* 
   The system has only one initiator but multiple responders, each with an unique tx/rx preamble code(pcode) for distinction
   In the ranging session, the initiator send poll message using different pcode in turn, only the responder with the same pcode will return the resp 
   message by means of which we can easily achieve one-to-many UWB ranging
*/

/* Default communication configuration. We use default non-STS DW mode. */
static dwt_config_t config = {
    9,               /* Channel number. */
    DWT_PLEN_128,    /* Preamble length. Used in TX only. */
    DWT_PAC8,        /* Preamble acquisition chunk size. Used in RX only. */
    9,               /* TX preamble code. Used in TX only. */
    9,               /* RX preamble code. Used in RX only. */
    1,               /* 0 to use standard 8 symbol SFD, 1 to use non-standard 8 symbol, 2 for non-standard 16 symbol SFD and 3 for 4z 8 symbol SDF type */
    DWT_BR_6M8,      /* Data rate. */
    DWT_PHRMODE_STD, /* PHY header mode. */
    DWT_PHRRATE_STD, /* PHY header rate. */
    (129 + 8 - 8),   /* SFD timeout (preamble length + 1 + SFD length - PAC size). Used in RX only. */
    DWT_STS_MODE_OFF, /* STS disabled */
    DWT_STS_LEN_64,/* STS length see allowed values in Enum dwt_sts_lengths_e */
    DWT_PDOA_M0      /* PDOA mode off */
};

static uint8_t uCurrentTrim_val;

/* Inter-ranging delay period, in milliseconds. */
#define RNG_DELAY_MS 10

/* Default antenna delay values for 64 MHz PRF. See NOTE 1 below. */
#define TX_ANT_DLY 16385
#define RX_ANT_DLY 16385

/* Frames used in the ranging process. See NOTE 2 below. */
static uint8_t rx_poll_msg[] = {0x41, 0x88, 0, 0xCA, 0xDE, 'W', 'A', 'V', 'E', 0x21, 0, 0};
static uint8_t rx_poll_msg_anchor[] = {0x41, 0x88, 0, 0xCA, 0xDE, 'R', 'E', 'S', 'P', 0x21, 0, 0};
// 加入final_tx_time
//static uint8_t rx_poll_msg_anchor[] = {0x41, 0x88, 0, 0xCA, 0xDE, 'R', 'E', 'S', 'P', 0x21, 0, 0, 0, 0, 0};
//#define RESP_MSG_LEN 15

/* Poll Message (rx_poll_msg) */
//|--FCF (2 byte)--|--Seq Num (1 byte)--|--Dest PAN ID (2 byte)--|--Payload (7 byte)--|
//|----------------------------------12 byte------------------------------------------|
//|--FCF (2 byte)--|--Seq Num (1 byte)--|--Dest PAN ID (2 byte)--|--Payload (7 byte)--|
//|----------------------------------12 byte------------------------------------------|

static uint8_t tx_resp_msg[] = {0x41, 0x88, 0, 0xCA, 0xDE, 'V', 'E', 'W', 'A', 0x10, 0x02, 0, 0, 0, 0};
static uint8_t rx_final_msg[] = {0x41, 0x88, 0, 0xCA, 0xDE, 'W', 'A', 'V', 'E', 0x23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

static uint8_t msg_common[] = {0x41, 0x88, 0, 0xCA, 0xDE, 'W', 'A', 'V', 'E', 0x21};
/* Length of the common part of the message (up to and including the function code, see NOTE 2 below). */
#define ALL_MSG_COMMON_LEN 10
/* Indexes to access some of the fields in the frames defined above. */
#define ALL_MSG_SN_IDX 2
//#define FINAL_MSG_POLL_TX_TS_IDX 10
#define FINAL_MSG_RESP_RX_TS_IDX 14
#define FINAL_MSG_FINAL_TX_TS_IDX 18

#define FINAL2_MSG_FINAL_TX_CIR_IDX 10
#define FINAL2_MSG_FINAL_TX_FP_IDX 106

#define POLL_TX_TO_RESP_RX_DLY_UUS 650
#define RESP_RX_TIMEOUT_UUS 1000

/* Frame sequence number, incremented after each transmission. */
static uint8_t frame_seq_nb = 0;

/* Buffer to store received messages.
 * Its size is adjusted to longest frame that this example code is supposed to handle. */
#define RX_BUF_LEN 128
static uint8_t rx_buffer[RX_BUF_LEN];

/* Hold copy of status register state here for reference so that it can be examined at a debug breakpoint. */
static uint32_t status_reg = 0;

/* Delay between frames, in UWB microseconds. See NOTE 4 below. */
/* This is the delay from Frame RX timestamp to TX reply timestamp used for calculating/setting the DW IC's delayed TX function. This includes the
 * frame length of approximately 190 us with above configuration. */
#define POLL_RX_TO_RESP_TX_DLY_UUS 600

/* This is the delay from the end of the frame transmission to the enable of the receiver, as programmed for the DW IC's wait for response feature. */
#define RESP_TX_TO_FINAL_RX_DLY_UUS 400
//#define RESP_TX_TO_FINAL_RX_DLY_UUS 0

/* Receive final timeout. See NOTE 5 below. */
#define FINAL_RX_TIMEOUT_UUS 0
//#define FINAL_RX_TIMEOUT_UUS 250
//#define FINAL_RX_TIMEOUT_UUS 0
/* Preamble timeout, in multiple of PAC size. See NOTE 6 below. */
#define PRE_TIMEOUT 0


/* Timestamps of frames transmission/reception. */
static uint64_t poll_rx_ts;
static uint64_t poll_tx_ts;
static uint64_t resp_tx_ts;
static uint64_t final_rx_ts;

/* Hold copies of computed time of flight and distance here for reference so that it can be examined at a debug breakpoint. */
static double tof;
static double distance;
/* Values for the PG_DELAY and TX_POWER registers reflect the bandwidth and power of the spectrum at the current
 * temperature. These values can be calibrated prior to taking reference measurements. See NOTE 2 below. */
extern dwt_txconfig_t txconfig_options;
extern dwt_txconfig_t txconfig_options_ch9;

#define CIR_LEN (16)

/* CIR-related parameters*/
static uint16_t cir_length = CIR_LEN;

#define LCD_BUFF_LEN (500)
static uint8_t usbVCOMout[LCD_BUFF_LEN * 8];

static int n = 0;

static uint8_t cir_buffer_tag[CIR_LEN * 6 + 1];
static uint8_t cir_buffer_anchor[CIR_LEN * 6 + 1];
static uint8_t cir_buffer3[CIR_LEN * 6 + 1];

struct uint24_t
{
    uint8_t lo;
    uint8_t mi;
    uint8_t hi;
};

struct cir_tap_struct
{
    struct uint24_t real;
    struct uint24_t imag;
};

void dw_init_part1()
{
    /* Reset DW IC */
    reset_DWIC(); /* Target specific drive of RSTn line into DW IC low for a period. */

    Sleep(2); // Time needed for DW3000 to start up (transition from INIT_RC to IDLE_RC

    /* Probe for the correct device driver. */
    //dwt_probe((struct dwt_probe_s *)&dw3000_probe_interf);

    while (!dwt_checkidlerc()) /* Need to make sure DW IC is in IDLE_RC before proceeding */
    {
    };

    if (dwt_initialise(DWT_DW_INIT) == DWT_ERROR)
    {
        // test_run_info((unsigned char *)"INIT FAILED     ");
        UART_WriteData((unsigned char *)"INIT FAILED     ", sizeof("INIT FAILED     "));
        while (1)
        {
        };
    }

    /* Enabling LEDs here for debug so that for each TX the D1 LED will flash on DW3000 red eval-shield boards.
     * Note, in real low power applications the LEDs should not be used. */
    dwt_setleds(DWT_LEDS_ENABLE | DWT_LEDS_INIT_BLINK);
}

void dw_init_part2(dwt_txconfig_t txconfig_options)
{
    /* Configure the TX spectrum parameters (power, PG delay and PG count) */
    dwt_configuretxrf(&txconfig_options);

    /* Apply default antenna delay value. See NOTE 1 below. */
    dwt_setrxantennadelay(RX_ANT_DLY);
    dwt_settxantennadelay(TX_ANT_DLY);

    /* Next can enable TX/RX states output on GPIOs 5 and 6 to help debug, and also TX/RX LEDs
     * Note, in real low power applications the LEDs should not be used. */
    //dwt_setlnapamode(DWT_LNA_ENABLE);
    dwt_setlnapamode(0);
    //dwt_setfinegraintxseq(0);
}

void dw_configure(dwt_config_t config)
{
    /* Configure DW IC. See NOTE 15 below. */
    /* if the dwt_configure returns DWT_ERROR either the PLL or RX calibration has failed the host should reset the device */
    if (dwt_configure(&config))
    {
        // test_run_info((unsigned char *)"CONFIG FAILED     ");
        UART_WriteData((unsigned char *)"CONFIG FAILED     ", sizeof("CONFIG FAILED     "));
        while (1)
        {
        };
    }
}

static uint8_t uCurrentTrim_val;

#define TARGET_XTAL_OFFSET_VALUE_PPM_MIN (3.0f)
#define TARGET_XTAL_OFFSET_VALUE_PPM_MAX (6.0f)

/* The FS_XTALT_MAX_VAL defined the maximum value of the trimming value */
#define FS_XTALT_MAX_VAL (XTAL_TRIM_BIT_MASK)

/* The typical trimming range (with 4.7pF external caps is ~77ppm (-65ppm to +12ppm) over all steps, see DW3000 Datasheet */
#define AVG_TRIM_PER_PPM ((FS_XTALT_MAX_VAL + 1) / 77.0f)

/*! ------------------------------------------------------------------------------------------------------------------
 * @fn ds_twr_responder()
 *
 * @brief Application entry point.
 *
 * @param  none
 *
 * @return none
 */

int ds_twr_responder(void)
{
    /* Configure the source address */
    msg_common[8] = ANCHOR_ID;
    /* Display application name on LCD. */
    // test_run_info((unsigned char *)APP_NAME);
    //UART_WriteData((unsigned char *)APP_NAME, sizeof(APP_NAME));

    /* Configure SPI rate, DW3000 supports up to 36 MHz */
    port_set_dw_ic_spi_fastrate();

    dw_init_part1();

    dw_configure(config);

    dw_init_part2(txconfig_options_ch9);

    uint8_t current_idx = 0;

    dwt_rxdiag_t rx_diag1;
    dwt_rxdiag_t rx_diag2;
    dwt_rxdiag_t rx_diag3;

    //dwt_nlos_ipdiag_t fp_diag1;
    //dwt_nlos_ipdiag_t fp_diag2;
    //dwt_nlos_ipdiag_t fp_diag3;

    dwt_configciadiag(DW_CIA_DIAG_LOG_ALL); // CIA to log the whole set of diagnostic registers

    /* Loop forever responding to ranging requests. */
    while (1)
    {

        dwt_setpreambledetecttimeout(0); // sets the receiver to timeout (and disable) when no preamble is received within the specified time
        /* Clear reception timeout to start next ranging process. */
        dwt_setrxtimeout(0);

        /* Activate reception immediately. */
        dwt_rxenable(DWT_START_RX_IMMEDIATE);

        /* Poll for reception of a frame or error/timeout. See NOTE 8 below. */
        //waitforsysstatus(&status_reg, NULL, (DWT_INT_RXFCG_BIT_MASK | SYS_STATUS_ALL_RX_TO | SYS_STATUS_ALL_RX_ERR), 0);
        while (!((status_reg = dwt_read32bitreg(SYS_STATUS_ID)) & (SYS_STATUS_RXFCG_BIT_MASK | SYS_STATUS_ALL_RX_TO | SYS_STATUS_ALL_RX_ERR)))
        { };

        //if (status_reg & DWT_INT_RXFCG_BIT_MASK)
        if (status_reg & SYS_STATUS_RXFCG_BIT_MASK)
        {

            // test_run_info((unsigned char *)"Received a frame  \r\n");
            uint16_t frame_len;

            /* Clear good RX frame event in the DW IC status register. */
            dwt_write32bitreg(SYS_STATUS_ID, SYS_STATUS_RXFCG_BIT_MASK);

            /* A frame has been received, read it into the local buffer. */
            frame_len = dwt_read32bitreg(RX_FINFO_ID) & FRAME_LEN_MAX_EX;
            if (frame_len <= RX_BUF_LEN)
            {
                dwt_readrxdata(rx_buffer, frame_len, 0);
            }
            // debug a2&a3
            
            // Distinguish message source (from tag or from anchor)
            bool is_from_tag;
            bool is_from_anchor;
            if (memcmp(&rx_buffer[5], "WAVE", 4) == 0) {
              is_from_tag = 1; 
              is_from_anchor=0;
            }
            else if (memcmp(&rx_buffer[5], "RESP", 4) == 0) {
              is_from_tag = 0; 
              is_from_anchor=1;
            }

            current_idx = rx_buffer[ALL_MSG_SN_IDX];

            uint32_t resp_tx_time;
            // int ret;
            
            // 读取接收时间ToA
            poll_rx_ts = get_rx_timestamp_u64();
            // 读取接收相位POA
            uint8_t temp[DB_MAX_DIAG_SIZE];
            dwt_readfromdevice(IP_TOA_LO_ID, 0, 108, temp);
            dwt_readdiagnostics(&rx_diag1);
            uint16_t ipatovPOA1 = rx_diag1.ipatovPOA; // POA from Ipatov preamble CIR
            uint16_t ipatovFpIndex1 = ((uint16_t)temp[IP_DIAG_8_ID - IP_TOA_LO_ID + 1] << 8 | temp[IP_DIAG_8_ID - IP_TOA_LO_ID])>>6;
            // dwt_readaccdata(cir_buffer_tag, 1+6, ipatovFpIndex1+1);
            // Read CIR
            if (is_from_tag){
              dwt_readaccdata(cir_buffer_tag, 1+6, ipatovFpIndex1+1);
            }
            else if (is_from_anchor){
              dwt_readaccdata(cir_buffer_anchor, 1+6, ipatovFpIndex1+1);
            }

            poll_rx_ts = get_rx_timestamp_u64();
            
            uint8_t* buffer_to_use = NULL;
            if (ANCHOR_ID == 0 && is_from_tag){
              buffer_to_use = cir_buffer_tag;
              // send message to another anchor
              /* Set expected response's delay and timeout. See NOTE 4, 5 and 7 below.
              * As this example only handles one incoming frame with always the same delay and timeout, those values can be set here once for all. */
              dwt_setrxaftertxdelay(POLL_TX_TO_RESP_RX_DLY_UUS);
              dwt_setrxtimeout(0);
              dwt_setpreambledetecttimeout(0);

              rx_poll_msg_anchor[ALL_MSG_SN_IDX] = frame_seq_nb; // 将当前帧序列号写入将要发送的消息中

              uint32_t final_tx_time;
              final_tx_time = (poll_rx_ts + (3000 * UUS_TO_DWT_TIME)) >> 8; // 计算延迟发送的时间戳 final_tx_time
              // 写入发射时间
              //rx_poll_msg_anchor[11] = (uint8_t)(final_tx_time & 0xFF);
              //rx_poll_msg_anchor[12] = (uint8_t)((final_tx_time >> 8) & 0xFF);
              //rx_poll_msg_anchor[13] = (uint8_t)((final_tx_time >> 16) & 0xFF);
              //rx_poll_msg_anchor[14] = (uint8_t)((final_tx_time >> 24) & 0xFF);

              dwt_writetxdata(sizeof(rx_poll_msg_anchor), rx_poll_msg_anchor, 0); // 将准备好的数据 rx_poll_msg_anchor 写入 DW3000 的 TX 缓冲区，长度为消息的字节数，偏移为 0
              dwt_writetxfctrl(sizeof(rx_poll_msg_anchor) + FCS_LEN, 0, 1); // 发射控制参数：包括帧总长度（加上帧校验 FCS）、偏移为 0，以及启用立即发射（1 表示标准帧）
              //dwt_writetxdata(RESP_MSG_LEN, rx_poll_msg_anchor, 0);
              //dwt_writetxfctrl(RESP_MSG_LEN + FCS_LEN, 0, 1);

              dwt_setdelayedtrxtime(final_tx_time); // 设置 DW3000 的延迟发射时间点为 final_tx_time
              int ret = dwt_starttx(DWT_START_TX_DELAYED); // 以延迟模式启动发送（发送将在 final_tx_time 时刻执行），返回值表示是否成功

              if (ret == DWT_SUCCESS){
                while (!(dwt_read32bitreg(SYS_STATUS_ID) & SYS_STATUS_TXFRS_BIT_MASK)){ }; // 等待直到发送完成（TX Frame Sent 位被置位），这是一个阻塞等待

                poll_tx_ts = get_tx_timestamp_u64();

                dwt_write32bitreg(SYS_STATUS_ID, SYS_STATUS_TXFRS_BIT_MASK); // 清除 TXFRS 位，复位发送完成的状态标志，准备好下一次通信
              }
            }
            else if (ANCHOR_ID == 1 && is_from_tag){
                buffer_to_use = cir_buffer_tag;
            }
            else if (ANCHOR_ID == 1 && is_from_anchor){
                buffer_to_use = cir_buffer_anchor;
            }

            if (buffer_to_use != NULL){
                n = 0;
                // 加一个字段来区分是来自tag还是anchor
                char source_flag = is_from_tag ? 'T' : 'A';  // T for Tag, A for Anchor
                n += sprintf((char *)&usbVCOMout[n], "%c,", source_flag);  // 加来源字段
                n += sprintf((char *)&usbVCOMout[n], "%02x%02x%02x,%02x%02x%02x,", buffer_to_use[3],buffer_to_use[2],buffer_to_use[1],buffer_to_use[6],buffer_to_use[5],buffer_to_use[4]);
                uint32_t final_tx_time = 0;
                //if (buffer_to_use[10] || buffer_to_use[11] || buffer_to_use[12] || buffer_to_use[13]) {
                //  final_tx_time = ((uint32_t)buffer_to_use[13] << 24) |
                //        ((uint32_t)buffer_to_use[12] << 16) |
                //        ((uint32_t)buffer_to_use[11] << 8) |
                //        ((uint32_t)buffer_to_use[10]);
                //  }
                n += sprintf((char *)&usbVCOMout[n], "%010llx,%010llx,%04x,%02x\n", poll_rx_ts, poll_tx_ts, ipatovPOA1, current_idx);
                //n += sprintf((char *)&usbVCOMout[n], "%010llx,%04x,%02x,%08x\n", poll_rx_ts, ipatovPOA1, current_idx, final_tx_time);
                UART_WriteData((uint8_t *)usbVCOMout, n);
                n = 0;
              }
        }      
        else{}
    }
}
#endif
///*****************************************************************************************************************************************************
// * NOTES:
// *
// * 1. The sum of the values is the TX to RX antenna delay, experimentally determined by a calibration process. Here we use a hard coded typical value
// *    but, in a real application, each device should have its own antenna delay properly calibrated to get the best possible precision when performing
// *    range measurements.
// * 2. The messages here are similar to those used in the DecaRanging ARM application (shipped with EVK1000 kit). They comply with the IEEE
// *    802.15.4 standard MAC data frame encoding and they are following the ISO/IEC:24730-62:2013 standard. The messages used are:
// *     - a poll message sent by the initiator to trigger the ranging exchange.
// *     - a response message sent by the responder allowing the initiator to go on with the process
// *     - a final message sent by the initiator to complete the exchange and provide all information needed by the responder to compute the
// *       time-of-flight (distance) estimate.
// *    The first 10 bytes of those frame are common and are composed of the following fields:
// *     - byte 0/1: frame control (0x8841 to indicate a data frame using 16-bit addressing).
// *     - byte 2: sequence number, incremented for each new frame.
// *     - byte 3/4: PAN ID (0xDECA).
// *     - byte 5/6: destination address, see NOTE 3 below.
// *     - byte 7/8: source address, see NOTE 3 below.
// *     - byte 9: function code (specific values to indicate which message it is in the ranging process).
// *    The remaining bytes are specific to each message as follows:
// *    Poll message:
// *     - no more data
// *    Response message:
// *     - byte 10: activity code (0x02 to tell the initiator to go on with the ranging exchange).
// *     - byte 11/12: activity parameter, not used for activity code 0x02.
// *    Final message:
// *     - byte 10 -> 13: poll message transmission timestamp.
// *     - byte 14 -> 17: response message reception timestamp.
// *     - byte 18 -> 21: final message transmission timestamp.
// *    All messages end with a 2-byte checksum automatically set by DW IC.
// * 3. Source and destination addresses are hard coded constants in this example to keep it simple but for a real product every device should have a
// *    unique ID. Here, 16-bit addressing is used to keep the messages as short as possible but, in an actual application, this should be done only
// *    after an exchange of specific messages used to define those short addresses for each device participating to the ranging exchange.
// * 4. Delays between frames have been chosen here to ensure proper synchronisation of transmission and reception of the frames between the initiator
// *    and the responder and to ensure a correct accuracy of the computed distance. The user is referred to DecaRanging ARM Source Code Guide for more
// *    details about the timings involved in the ranging process.
// *    Initiator: |Poll TX| ..... |Resp RX| ........ |Final TX|
// *    Responder: |Poll RX| ..... |Resp TX| ........ |Final RX|
// *                   ^|P RMARKER|                                    - time of Poll TX/RX
// *                                   ^|R RMARKER|                    - time of Resp TX/RX
// *                                                      ^|R RMARKER| - time of Final TX/RX
// *
// *                       <--TDLY->                                   - POLL_TX_TO_RESP_RX_DLY_UUS (RDLY-RLEN)
// *                               <-RLEN->                            - RESP_RX_TIMEOUT_UUS   (length of poll frame)
// *                    <----RDLY------>                               - POLL_RX_TO_RESP_TX_DLY_UUS (depends on how quickly responder
// *                                                                                                                      can turn around and reply)
// *
// *
// *                                        <--T2DLY->                 - RESP_TX_TO_FINAL_RX_DLY_UUS (R2DLY-FLEN)
// *                                                  <-FLEN--->       - FINAL_RX_TIMEOUT_UUS   (length of response frame)
// *                                    <----RDLY--------->            - RESP_RX_TO_FINAL_TX_DLY_UUS (depends on how quickly initiator
// *                                                                                                                      can turn around and reply)
// *
// * EXAMPLE 1: with SPI rate set to 18 MHz (default on this platform), and frame lengths of ~190 us, the delays can be set to:
// *            POLL_RX_TO_RESP_TX_DLY_UUS of 400uus, and RESP_RX_TO_FINAL_TX_DLY_UUS of 400uus (TXtoRX delays are set to 210uus)
// *            reducing the delays further can be achieved by using interrupt to handle the TX/RX events, or other code optimisations/faster SPI
// *
// * EXAMPLE 2: with SPI rate set to 4.5 MHz, and frame lengths of ~190 us, the delays can be set to:
// *            POLL_RX_TO_RESP_TX_DLY_UUS of 550uus, and RESP_RX_TO_FINAL_TX_DLY_UUS of 600uus (TXtoRX delays are set to 360 and 410 uus respectively)
// *
// * 5. This timeout is for complete reception of a frame, i.e. timeout duration must take into account the length of the expected frame. Here the value
// *    is arbitrary but chosen large enough to make sure that there is enough time to receive the complete final frame sent by the responder at the
// *    6.81 Mbps data rate used (around 220 us).
// * 6. The preamble timeout allows the receiver to stop listening in situations where preamble is not starting (which might be because the responder is
// *    out of range or did not receive the message to respond to). This saves the power waste of listening for a message that is not coming. We
// *    recommend a minimum preamble timeout of 5 PACs for short range applications and a larger value (e.g. in the range of 50% to 80% of the preamble
// *    length) for more challenging longer range, NLOS or noisy environments.
// * 7. In a real application, for optimum performance within regulatory limits, it may be necessary to set TX pulse bandwidth and TX power, (using
// *    the dwt_configuretxrf API call) to per device calibrated values saved in the target system or the DW IC OTP memory.
// * 8. We use polled mode of operation here to keep the example as simple as possible but all status events can be used to generate interrupts. Please
// *    refer to DW IC User Manual for more details on "interrupts". It is also to be noted that STATUS register is 5 bytes long but, as the event we
// *    use are all in the first bytes of the register, we can use the simple dwt_read32bitreg() API call to access it instead of reading the whole 5
// *    bytes.
// * 9. Timestamps and delayed transmission time are both expressed in device time units so we just have to add the desired response delay to poll RX
// *    timestamp to get response transmission time. The delayed transmission time resolution is 512 device time units which means that the lower 9 bits
// *    of the obtained value must be zeroed. This also allows to encode the 40-bit value in a 32-bit words by shifting the all-zero lower 8 bits.
// * 10. dwt_writetxdata() takes the full size of the message as a parameter but only copies (size - 2) bytes as the check-sum at the end of the frame is
// *     automatically appended by the DW IC. This means that our variable could be two bytes shorter without losing any data (but the sizeof would not
// *     work anymore then as we would still have to indicate the full length of the frame to dwt_writetxdata()).
// * 11. When running this example on the DWK3000 platform with the POLL_RX_TO_RESP_TX_DLY response delay provided, the dwt_starttx() is always
// *     successful. However, in cases where the delay is too short (or something else interrupts the code flow), then the dwt_starttx() might be issued
// *     too late for the configured start time. The code below provides an example of how to handle this condition: In this case it abandons the
// *     ranging exchange and simply goes back to awaiting another poll message. If this error handling code was not here, a late dwt_starttx() would
// *     result in the code flow getting stuck waiting subsequent RX event that will will never come. The companion "initiator" example (ex_05a) should
// *     timeout from awaiting the "response" and proceed to send another poll in due course to initiate another ranging exchange.
// * 12. The high order byte of each 40-bit time-stamps is discarded here. This is acceptable as, on each device, those time-stamps are not separated by
// *     more than 2**32 device time units (which is around 67 ms) which means that the calculation of the round-trip delays can be handled by a 32-bit
// *     subtraction.
// * 13. The user is referred to DecaRanging ARM application (distributed with EVK1000 product) for additional practical example of usage, and to the
// *     DW IC API Guide for more details on the DW IC driver functions.
// * 14. In this example, the DW IC is put into IDLE state after calling dwt_initialise(). This means that a fast SPI rate of up to 36 MHz can be used
// *     thereafter.
// * 15. Desired configuration by user may be different to the current programmed configuration. dwt_configure is called to set desired
// *     configuration.
// ****************************************************************************************************************************************************/