void vectorAdd(int va[], int vb[], int n, int result[]) {
    for (int i = 0; i < n; ++i) {
        result[i] = va[i] + vb[i];
    }
}

void vectorMul(int va[], int vb[], int n, int result[]) {
    for (int i = 0; i < n; ++i) {
        result[i] = va[i] * vb[i];
    }
}

int main(void) {
    int size = 4;

    int vectA[4] = {1, 2, 3, 4};
    int vectB[4] = {1, 2, 3, 4};
    int vectC[4] = {10, 10, 10, 10};
    int result[4] = {0};

    vectorMul(vectA, vectC, size, vectA);
    vectorMul(vectB, vectC, size, vectB);
    vectorAdd(vectA, vectB, size, result);
}