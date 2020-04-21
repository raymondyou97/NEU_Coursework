#include "Arithmetic.h"
#include <unistd.h>
#include <iostream>
using namespace std;
int main()
{
	int num1, num2;
	cout << "Please enter integer 1" << endl;
	cin >> num1;
	cout << "Please enter integer 2" << endl;
	cin >> num2;
	Arithmetic arith;
	arith.RegisterWrite(A_offset, num1);
	arith.RegisterWrite(B_offset, num2);
	for(int i = 0; i < 4; i++) {
		arith.RegisterWrite(code_offset, i);
		if(i == 0) {
			cout << "Sum: ";
		}
		if(i == 1) {
			cout << "Difference: ";
		}
		if(i == 2) {
			cout << "Product: ";
		}
		if(i == 3) {
			cout << "Bitwise AND: ";
		}
		cout << arith.RegisterRead(Y_offset) << endl;
	}
}
