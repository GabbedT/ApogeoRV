#include <stdint.h>

#define CLOCK_FREQ 100000000 /* 100 MHz */

/* Base addresses */
#define LED 0x00000800
#define SWITCH 0x00000880
#define TIMER 0x00000900

uint32_t volatile * const gLedBase = (uint32_t *) LED;
uint32_t volatile * const gTimerBase = (uint32_t *) TIMER;

void blink() {
    /* Start with led OFF */
    *gLedBase = 0; 

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
    /* Invert the led */
    *gLedBase = ~(*gLedBase); 

    /* Reset the timer */
    *(gTimerBase + 3) = 0; *(gTimerBase + 2) = 0;
}