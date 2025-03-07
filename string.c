void puts(char *s) {
    return syscall(3, s);
}

int main() {
    puts("foobar" "baz\n");
}
