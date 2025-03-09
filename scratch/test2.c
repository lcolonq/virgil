int newx(int x) {
    return (x + 1) + (x + 1);
}

int main() {
	int x = 0;
    while (x < 10) {
        x = newx(x);
    }
}
