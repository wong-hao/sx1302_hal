/*
 / _____)             _              | |
( (____  _____ ____ _| |_ _____  ____| |__
 \____ \| ___ |    (_   _) ___ |/ ___)  _ \
 _____) ) ____| | | || |_| ____( (___| | | |
(______/|_____)_|_|_| \__)_____)\____)_| |_|
  (C)2019 Semtech

Description:
    LoRa concentrator HAL common auxiliary functions

License: Revised BSD License, see LICENSE.TXT file include in the project
*/


#ifndef _LORAGW_AUX_H
#define _LORAGW_AUX_H

/* -------------------------------------------------------------------------- */
/* --- DEPENDANCIES --------------------------------------------------------- */

#include "config.h"    /* library configuration options (dynamically generated) */

/* -------------------------------------------------------------------------- */
/* --- PUBLIC MACROS -------------------------------------------------------- */

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))

/**
@brief Get a particular bit value from a byte
@param b [in]   Any byte from which we want a bit value
@param p [in]   Position of the bit in the byte [0..7]
@param n [in]   Number of bits we want to get
@return The value corresponding the requested bits
*/
#define TAKE_N_BITS_FROM(b, p, n) (((b) >> (p)) & ((1 << (n)) - 1))

/* -------------------------------------------------------------------------- */
/* --- PUBLIC FUNCTIONS PROTOTYPES ------------------------------------------ */

/**
@brief Wait for a certain time (millisecond accuracy)
@param t number of milliseconds to wait.
*/
void wait_ms(unsigned long t);

#endif

/* --- EOF ------------------------------------------------------------------ */
