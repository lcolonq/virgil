int add(int x, int b) {
	int res = x;
	res += b;
	return res;
}

int main() {
	int x = 5;
	int y = x + x;
	int z = add(x, y);
}
