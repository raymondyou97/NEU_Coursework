// Add your program here!

#include <stdio.h>

double power(double base, double n) {
	printf("%f\n", base);
	double current = base;
    	double i;
	for(i = 1; i < n; i++) {
		current *= base;
		printf("%f\n", current);
	}
	return current;
}		

int main() {
	power(2.0, 10.0);
	return 0;
}
