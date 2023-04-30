#include <iostream>
#include <fstream>
#include <array>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define PREDICTIONS 1000

#define CHUNK 10

struct branch_entry {
    int iaddress; 
    int branchAddress;
    int taken; 
};


void fowardPattern(int *address);

void backwardPattern(int *address); 

void randomPattern(int *address);

void alternatingPattern(int *address);

int main(void) {

    int startAddress = -4;
    int endAddress = startAddress + (PREDICTIONS << 2);

    std::cout << "Start address: " + std::to_string(startAddress) + "\n"; 
    std::cout << "End address: " + std::to_string(endAddress) + "\n"; 

    int times = PREDICTIONS / (CHUNK * 4); 

    for (int i = 0; i < times; ++i) {
        fowardPattern(&startAddress); 
        backwardPattern(&startAddress); 
        randomPattern(&startAddress); 
        alternatingPattern(&startAddress); 
    }
}


/* Generate 10 branch entries always taken */
void fowardPattern(int *address) {
    std::ofstream file; 

    file.open("predictions.txt", std::ios::app);

    struct branch_entry t;

    for (int i = 0; i < CHUNK; ++i) {
        t.iaddress = *address + 4;
        t.branchAddress = t.iaddress + 4;
        t.taken = 1;
        file << t.iaddress << " " << t.branchAddress  << " " << t.taken << std::endl; 

        /* Update address */
        *address = t.iaddress; 
    }
} 

/* Generate 10 branch entries always not taken */
void backwardPattern(int *address) {
    std::ofstream file; 

    file.open("predictions.txt", std::ios::app);

    struct branch_entry t;

    for (int i = 0; i < CHUNK; ++i) {
        t.iaddress = *address + 4;
        t.branchAddress = t.iaddress + 4;
        t.taken = 0;
        file << t.iaddress << " " << t.branchAddress  << " " << t.taken << std::endl; 

        /* Update address */
        *address = t.iaddress;
    }
} 


/* Generate 10 random branch entries */
void randomPattern(int *address) {
    srand(time(NULL)); 
    std::ofstream file; 

    file.open("predictions.txt", std::ios::app);

    struct branch_entry t;

    for (int i = 0; i < CHUNK; ++i) {
        t.iaddress = *address + 4;
        t.branchAddress = t.iaddress + 4;
        t.taken = ((rand() % 100) > 50) ? 1 : 0;
        file << t.iaddress << " " << t.branchAddress  << " " << t.taken << std::endl; 

        /* Update address */
        *address = t.iaddress;
    }
} 

/* Generate 10 random branch entries */
void alternatingPattern(int *address) {
    srand(time(NULL)); 
    std::ofstream file; 

    file.open("predictions.txt", std::ios::app);

    struct branch_entry t;

    for (int i = 0; i < CHUNK; ++i) {
        t.iaddress = *address + 4;
        t.branchAddress = t.iaddress + 4;
        t.taken = (i % 2) ? 1 : 0;
        file << t.iaddress << " " << t.branchAddress  << " " << t.taken << std::endl; 

        /* Update address */
        *address = t.iaddress;
    }
}