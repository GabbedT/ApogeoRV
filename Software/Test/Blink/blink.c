#include <stdint.h>

#define CLOCK_FREQ 100000000 /* 100 MHz */

/* Base addresses */
#define LED 0x00000800
#define SWITCH 0x00000880
#define TIMER 0x00000900

uint32_t volatile * const gLedBase = (uint32_t *) LED;
uint32_t volatile * const gTimerBase = (uint32_t *) TIMER;

uint32_t volatile gLedIndex = 0;
uint32_t volatile gLedMode = 0; 

void blink() {
    /* Start with LED 0 ON */
    *(gLedBase + gLedIndex) = 1; 

    /* Setup interrupt time */
    *gTimerBase = CLOCK_FREQ / 2; *(gTimerBase + 1) = 0;

    /* Reset the timer */
    *(gTimerBase + 3) = 0; *(gTimerBase + 2) = 0;

    while (1) {
        /* Wait for the timer interrupt */
        asm volatile ("wfi");
    }
}

__attribute__((interrupt)) void timer_handler() {
    if (gLedMode == 0) {
        /* Turn OFF the LED and turn ON the next */
        *(gLedBase + gLedIndex) = 0; 

        /* Wrap around to 0 at 15 */
        gLedIndex = (gLedIndex + 1) % 16; 
        *(gLedBase + gLedIndex) = 1;

        /* Change mode when finish */
        if (gLedIndex == 0) {
            gLedMode = 1;

            *gLedBase = 1; *(gLedBase + 15) = 1;
        }

        /* Reset the timer */
        *(gTimerBase + 3) = 0; *(gTimerBase + 2) = 0;
    } else {
        *(gLedBase + gLedIndex) = 0; *((gLedBase + 15) - gLedIndex) = 0;

        /* Wrap around to 0 at 8 */
        gLedIndex = (gLedIndex + 1) % 8;
        *(gLedBase + gLedIndex) = 1; *((gLedBase + 15) - gLedIndex) = 1;

        /* Reset the timer */
        *(gTimerBase + 3) = 0; *(gTimerBase + 2) = 0;

        /* Change mode when finish */
        if (gLedIndex == 0) {
            gLedMode = 0;

            *(gLedBase + 15) = 0;
        }
    }
}