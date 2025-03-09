typedef unsigned long size_t;

void *malloc(size_t n) {
    void *ret = 0;
    syscall(2, n, &ret);
    return ret;
}

void puts(char *s) {
    syscall(3, s);
}

int main() {
    char *test = malloc(5);
    test[0] = 't';
    test[1] = 'e';
    test[2] = 's';
    test[3] = 't';
    test[4] = 0;
    puts(test);
    puts("hello computer");
}
