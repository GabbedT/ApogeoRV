#include <stdio.h>

int jump_function1(int); 
int jump_function2(int); 

int main(void) {
    int sum = 0; 

    for (int i = 0; i < 20; ++i) {
        if ((i % 2) == 0) {
            sum += jump_function1(sum * i);
        } else {
            sum += jump_function2(sum * i); 
        }
    }

    /* SUM = 600 */
}

int jump_function1(int p) {
    if (p % 2 == 0) {
        return 20; 
    } else {
        return 25;
    }
}

int jump_function2(int p) {
    if (p % 2 == 0) {
        return 40; 
    } else {
        return 45;
    }
}