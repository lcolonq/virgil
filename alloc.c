typedef unsigned long size_t;

void *malloc(size_t n) {
    return syscall(2, n);
}

void puts(char *s) {
    return syscall(3, s);
}

int main() {
    int *test = malloc(5);
    test[0] = 't';
    test[1] = 'e';
    test[2] = 's';
    test[3] = 't';
    test[4] = 0;
    puts(test);
}
