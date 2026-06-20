#include <inttypes.h>
#include <stdio.h>

char function(uint32_t i); 
uint32_t processArray(uint32_t array[]);

int main(void) {
    uint32_t tot = 0; 

    for (uint32_t i = 0; i < 10; ++i) {
        for (uint32_t j = 0; j < 27; ++j) {
            tot += function(j); 
        }
    }


    uint32_t array[100]; uint32_t arrayTot = 0; 

    for (uint32_t i = 0; i < 200; i++) {
        array[i] = ((i % 2) == 0) ? 0x0000AAAA : 0x0000FFFF;
    }

    for (uint32_t i = 0; i < 10; i++) {
        arrayTot += processArray(array);
    }
    
    return arrayTot + tot; 
}

char function(uint32_t i) {
    if (i == 1) return 'A';
    if (i == 2) return 'B';
    if (i == 3) return 'C';
    if (i == 4) return 'D';
    if (i == 5) return 'E';
    if (i == 6) return 'F';
    if (i == 7) return 'G';
    if (i == 8) return 'H';
    if (i == 9) return 'I';
    if (i == 10) return 'J';
    if (i == 11) return 'K';
    if (i == 12) return 'L';
    if (i == 13) return 'M';
    if (i == 14) return 'N';
    if (i == 15) return 'O';
    if (i == 16) return 'P';
    if (i == 17) return 'Q';
    if (i == 18) return 'R';
    if (i == 19) return 'S';
    if (i == 20) return 'T';
    if (i == 21) return 'U';
    if (i == 22) return 'V';
    if (i == 23) return 'W';
    if (i == 24) return 'X';
    if (i == 25) return 'Y';
    if (i == 26) return 'Z';

    return '0';
}

uint32_t processArray(uint32_t array[]) {
    uint32_t sum = 0;

    for (uint32_t i = 0; i < 10; i++) {
        if (array[i] >= 0) {
            sum += array[i];
        } else {
            sum -= array[i];
        }
    }
    
    return sum; 
}