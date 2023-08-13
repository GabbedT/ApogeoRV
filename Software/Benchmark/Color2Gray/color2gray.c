#include <inttypes.h>
#include "image.h"

#define PIXEL_START 54

const uint32_t imageSize = 4234;

int main() {
    /* Pointer to buffer memory region that acts like a print function */
    uint8_t *bufferPtr = (uint8_t *) 0xFFFFFFFF;

    /* Extract image informations */
    uint32_t imageWidth = (image[0x15] << 24) | (image[0x14] << 16) | (image[0x13] << 8) | image[0x12];
    uint32_t imageHeight = (image[0x19] << 24) | (image[0x18] << 16) | (image[0x17] << 8) | image[0x16];

    uint32_t imagePixelSize = imageHeight * imageWidth * 3;

    uint32_t i = 0;
    
    while (i < imageSize) {
        if ((i >= PIXEL_START) && i < (imagePixelSize + PIXEL_START)) {
            /* Extract the gray color (B + G + R) / 3 */
            uint8_t p = (image[i] + image[i + 1] + image[i + 2]) / 3;

            /* Write to buffer */
            for (int j = 0; j < 3; ++j) {
                *bufferPtr = p;
            }

            i += 3;
        } else {
            *bufferPtr = image[i]; 

            ++i; 
        }
    }

    asm volatile ("ecall");
}