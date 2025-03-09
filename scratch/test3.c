int screen[10];

int main() {
    screen[0] = 0;
    screen[1] = 1;
    int i = 2;
    while (i < 10) {
        screen[i] = screen[i - 1] + screen[i - 2];
        i = i + 1;
    }
    i = 0;
    while (i < 10) {
        log(screen[i]);
        i = i + 1;
    }
    // log(screen);
    // while (1) {
    //     render();
    // }
}
