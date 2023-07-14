#include <inttypes.h>
#include <stdio.h>

uint64_t function(uint32_t data);

const uint8_t SECTOR[] = {
    0xFF, 0xEE, 0xDD, 0xCC, 0xBB, 0xAA
};

int main() {
    uint32_t data = 0xFFFFFFFF;
    data ^= (SECTOR[3] << 24) | (SECTOR[2] << 16) | (SECTOR[1] << 8) | SECTOR[0];
    printf("Data: %x\n", data);

    data = function(data) >> 32; 
    printf("Data: %x\n", data);

    return data;
}


uint64_t function(uint32_t data) {
    uint64_t longData = 1; 

    for (int i = 0; i < 6; ++i) {
        if (i != 0) { 
            printf("Branch Taken\n"); 
        }

        longData *= SECTOR[i];
        printf("Long: %lx\n", longData); 

        longData -= data; 
        printf("Long: %lx\n", longData);
    } 

    printf("Branch Exit\n"); 
    return longData; 
}