void inc(int **x, int *z) {
    **x = **x + 1;
    *x = z;
}

int main() {
    int x = 4141414141;
    int z = 10;
    int *y = &x;
    inc(&y, &z);
    x;
    z;
    *y;
}
