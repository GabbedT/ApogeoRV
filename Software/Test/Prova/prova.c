#include <inttypes.h>

const uint32_t CONSTANT = 0xFFFF3333; 

const uint8_t SECTOR[] = {
    0xFF, 0xEE, 0xDD, 0xCC, 0xBB, 0xAA
};

int main() {
    uint32_t data = 0xFFFFFFFF;
    data &= (16 << ~SECTOR[0]);

    uint64_t longData = 1; 

    for (int i = 0; i < 6; ++i) {
        longData *= SECTOR[i];
        longData -= data; 
    } 

    return longData; 
}