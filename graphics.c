int screen[640 * 400];

void main() {
    // while (1) {
    //     int now = get_time();
    //     render(&screen);
    //     int diff = get_time() - now;
    //     if (diff < 16) {
    //         sleep(16 - diff);
    //     }
    // }
    // log(screen);
    screen[10] = 16711680;
    while (1) {
        render(&screen);
    }
}
