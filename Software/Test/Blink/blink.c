#include <stdint.h>

void blink() {
    for (int i = 0; i < 20; ++i) {
        /* Wait for the timer interrupt */
        asm volatile ("wfi");
    }
}