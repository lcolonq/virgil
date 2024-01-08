int add(int x, int b) {
	int res;
	res = x;
	res = res + b;
	return res;
}

int main() {
	int x, y, z;
	x = 5;
	y = x + x;
	z = add(x, y);
}
