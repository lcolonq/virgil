typedef struct { int x, y; char c; } foo;

char bar(foo a) {
    return a.c;
}

int main() {
    foo x;
    x.x = 10;
    x.y = 20;
    x.c = 'a';
    int y = x.x;
    bar(x);
}
