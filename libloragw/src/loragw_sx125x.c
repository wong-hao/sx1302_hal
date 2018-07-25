/*
 / _____)             _              | |
( (____  _____ ____ _| |_ _____  ____| |__
 \____ \| ___ |    (_   _) ___ |/ ___)  _ \
 _____) ) ____| | | || |_| ____( (___| | | |
(______/|_____)_|_|_| \__)_____)\____)_| |_|
  (C)2018 Semtech

Description:
    TODO

License: Revised BSD License, see LICENSE.TXT file include in the project
*/

/* -------------------------------------------------------------------------- */
/* --- DEPENDANCIES --------------------------------------------------------- */

#include <stdint.h>     /* C99 types */
#include <stdbool.h>    /* bool type */
#include <stdio.h>      /* printf fprintf */
#include <string.h>     /* memset */
#include <sys/ioctl.h>
#include <linux/spi/spidev.h>

#include "loragw_sx125x.h"
#include "loragw_spi.h"
#include "loragw_aux.h"
#include "loragw_reg.h"
#include "loragw_hal.h"

/* -------------------------------------------------------------------------- */
/* --- PRIVATE MACROS ------------------------------------------------------- */

#define ARRAY_SIZE(a) (sizeof(a) / sizeof((a)[0]))
#if DEBUG_RAD == 1
    #define DEBUG_MSG(str)              fprintf(stderr, str)
    #define DEBUG_PRINTF(fmt, args...)  fprintf(stderr,"%s:%d: "fmt, __FUNCTION__, __LINE__, args)
    #define CHECK_NULL(a)               if(a==NULL){fprintf(stderr,"%s:%d: ERROR: NULL POINTER AS ARGUMENT\n", __FUNCTION__, __LINE__);return LGW_REG_ERROR;}
#else
    #define DEBUG_MSG(str)
    #define DEBUG_PRINTF(fmt, args...)
    #define CHECK_NULL(a)               if(a==NULL){return LGW_REG_ERROR;}
#endif

/* -------------------------------------------------------------------------- */
/* --- PRIVATE TYPES -------------------------------------------------------- */

/**
@struct lgw_radio_type_version_s
@brief Associate a radio type with its corresponding expected version value
        read in the radio version register.
*/
struct lgw_radio_type_version_s {
    enum lgw_radio_type_e type;
    uint8_t reg_version;
};

/* -------------------------------------------------------------------------- */
/* --- PRIVATE CONSTANTS ---------------------------------------------------- */

#define PLL_LOCK_MAX_ATTEMPTS 5

#define READ_ACCESS     0x00
#define WRITE_ACCESS    0x80

/* -------------------------------------------------------------------------- */
/* --- PRIVATE VARIABLES ---------------------------------------------------- */

extern void *lgw_spi_target; /*! generic pointer to the SPI device */

/* -------------------------------------------------------------------------- */
/* --- PRIVATE FUNCTIONS ---------------------------------------------------- */

/* Simple read */
int sx125x_reg_r(void *spi_target, uint8_t spi_mux_target, uint8_t address, uint8_t *data) {
    int spi_device;
    uint8_t out_buf[3];
    uint8_t command_size;
    uint8_t in_buf[ARRAY_SIZE(out_buf)];
    struct spi_ioc_transfer k;
    int a;

    /* check input variables */
    CHECK_NULL(spi_target);
    CHECK_NULL(data);

    spi_device = *(int *)spi_target; /* must check that spi_target is not null beforehand */

    /* prepare frame to be sent */
    out_buf[0] = spi_mux_target;
    out_buf[1] = READ_ACCESS | (address & 0x7F);
    out_buf[2] = 0x00;
    command_size = 3;

    /* I/O transaction */
    memset(&k, 0, sizeof(k)); /* clear k */
    k.tx_buf = (unsigned long) out_buf;
    k.rx_buf = (unsigned long) in_buf;
    k.len = command_size;
    k.cs_change = 0;
    a = ioctl(spi_device, SPI_IOC_MESSAGE(1), &k);

    /* determine return code */
    if (a != (int)k.len) {
        DEBUG_MSG("ERROR: SPI READ FAILURE\n");
        return LGW_SPI_ERROR;
    } else {
        DEBUG_MSG("Note: SPI read success\n");
        *data = in_buf[command_size - 1];
        return LGW_SPI_SUCCESS;
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

int sx125x_reg_w(void *spi_target, uint8_t spi_mux_target, uint8_t address, uint8_t data) {
    int spi_device;
    uint8_t out_buf[3];
    uint8_t command_size;
    struct spi_ioc_transfer k;
    int a;

    /* check input variables */
    CHECK_NULL(spi_target);

    spi_device = *(int *)spi_target; /* must check that spi_target is not null beforehand */

    /* prepare frame to be sent */
    out_buf[0] = spi_mux_target;
    out_buf[1] = WRITE_ACCESS | (address & 0x7F);
    out_buf[2] = data;
    command_size = 3;

    /* I/O transaction */
    memset(&k, 0, sizeof(k)); /* clear k */
    k.tx_buf = (unsigned long) out_buf;
    k.len = command_size;
    k.speed_hz = SPI_SPEED;
    k.cs_change = 0;
    k.bits_per_word = 8;
    a = ioctl(spi_device, SPI_IOC_MESSAGE(1), &k);

    /* determine return code */
    if (a != (int)k.len) {
        DEBUG_MSG("ERROR: SPI WRITE FAILURE\n");
        return LGW_SPI_ERROR;
    } else {
        DEBUG_MSG("Note: SPI write success\n");
        return LGW_SPI_SUCCESS;
    }
}

/* -------------------------------------------------------------------------- */
/* --- PRIVATE FUNCTIONS DEFINITION ----------------------------------------- */

void sx125x_write(uint8_t channel, uint8_t addr, uint8_t data) {
    sx125x_reg_w(lgw_spi_target, channel, addr, data);
    return;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

uint8_t sx125x_read(uint8_t channel, uint8_t addr) {
    uint8_t read_value;
    sx125x_reg_r(lgw_spi_target, channel, addr, &read_value);
    return (uint8_t)read_value;
}

/* -------------------------------------------------------------------------- */
/* --- PUBLIC FUNCTIONS DEFINITION ------------------------------------------ */

int lgw_setup_sx125x(uint8_t rf_chain, uint8_t rf_clkout, bool rf_enable, uint8_t rf_radio_type, uint32_t freq_hz) {
    uint32_t part_int = 0;
    uint32_t part_frac = 0;
    int cpt_attempts = 0;

    if (rf_chain >= LGW_RF_CHAIN_NB) {
        DEBUG_MSG("ERROR: INVALID RF_CHAIN\n");
        return -1;
    }

    /* Get version to identify SX1255/57 silicon revision */
    DEBUG_PRINTF("Note: SX125x #%d version register returned 0x%02x\n", rf_chain, sx125x_read(rf_chain, 0x07));

    /* General radio setup */
    if (rf_clkout == rf_chain) {
        sx125x_write(rf_chain, 0x10, SX125x_TX_DAC_CLK_SEL + 2);
        DEBUG_PRINTF("Note: SX125x #%d clock output enabled\n", rf_chain);
    } else {
        sx125x_write(rf_chain, 0x10, SX125x_TX_DAC_CLK_SEL);
        DEBUG_PRINTF("Note: SX125x #%d clock output disabled\n", rf_chain);
    }

    switch (rf_radio_type) {
        case LGW_RADIO_TYPE_SX1255:
            sx125x_write(rf_chain, 0x28, SX125x_XOSC_GM_STARTUP + SX125x_XOSC_DISABLE*16);
            break;
        case LGW_RADIO_TYPE_SX1257:
            sx125x_write(rf_chain, 0x26, SX125x_XOSC_GM_STARTUP + SX125x_XOSC_DISABLE*16);
            break;
        default:
            DEBUG_PRINTF("ERROR: UNEXPECTED VALUE %d FOR RADIO TYPE\n", rf_radio_type);
            break;
    }

    if (rf_enable == true) {
        /* Tx gain and trim */
        sx125x_write(rf_chain, 0x08, SX125x_TX_MIX_GAIN + SX125x_TX_DAC_GAIN*16);
        sx125x_write(rf_chain, 0x0A, SX125x_TX_ANA_BW + SX125x_TX_PLL_BW*32);
        sx125x_write(rf_chain, 0x0B, SX125x_TX_DAC_BW);

        /* Rx gain and trim */
        sx125x_write(rf_chain, 0x0C, SX125x_LNA_ZIN + SX125x_RX_BB_GAIN*2 + SX125x_RX_LNA_GAIN*32);
        sx125x_write(rf_chain, 0x0D, SX125x_RX_BB_BW + SX125x_RX_ADC_TRIM*4 + SX125x_RX_ADC_BW*32);
        sx125x_write(rf_chain, 0x0E, SX125x_ADC_TEMP + SX125x_RX_PLL_BW*2);

        /* set RX PLL frequency */
        switch (rf_radio_type) {
            case LGW_RADIO_TYPE_SX1255:
                part_int = freq_hz / (SX125x_32MHz_FRAC << 7); /* integer part, gives the MSB */
                part_frac = ((freq_hz % (SX125x_32MHz_FRAC << 7)) << 9) / SX125x_32MHz_FRAC; /* fractional part, gives middle part and LSB */
                break;
            case LGW_RADIO_TYPE_SX1257:
                part_int = freq_hz / (SX125x_32MHz_FRAC << 8); /* integer part, gives the MSB */
                part_frac = ((freq_hz % (SX125x_32MHz_FRAC << 8)) << 8) / SX125x_32MHz_FRAC; /* fractional part, gives middle part and LSB */
                break;
            default:
                DEBUG_PRINTF("ERROR: UNEXPECTED VALUE %d FOR RADIO TYPE\n", rf_radio_type);
                break;
        }

        sx125x_write(rf_chain, 0x01,0xFF & part_int); /* Most Significant Byte */
        sx125x_write(rf_chain, 0x02,0xFF & (part_frac >> 8)); /* middle byte */
        sx125x_write(rf_chain, 0x03,0xFF & part_frac); /* Least Significant Byte */

        /* start and PLL lock */
        do {
            if (cpt_attempts >= PLL_LOCK_MAX_ATTEMPTS) {
                DEBUG_MSG("ERROR: FAIL TO LOCK PLL\n");
                return -1;
            }
            sx125x_write(rf_chain, 0x00, 1); /* enable Xtal oscillator */
            sx125x_write(rf_chain, 0x00, 3); /* Enable RX (PLL+FE) */
            ++cpt_attempts;
            DEBUG_PRINTF("Note: SX125x #%d PLL start (attempt %d)\n", rf_chain, cpt_attempts);
            wait_ms(1);
        } while((sx125x_read(rf_chain, 0x11) & 0x02) == 0);
    } else {
        DEBUG_PRINTF("Note: SX125x #%d kept in standby mode\n", rf_chain);
    }

    return 0;
}

/* --- EOF ------------------------------------------------------------------ */