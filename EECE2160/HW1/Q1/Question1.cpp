#include <iostream>
#include <cmath>
#include <algorithm>
using namespace std;

//Prints all the bytes
void PrintBytes() {
	cout << "Number of bytes needed to store the following data types" << endl;
	cout << "bool: 1byte " << endl;
	cout << "char: 1byte" << endl;
	cout << "int: 4bytes" << endl;
	cout << "float: 4bytes" << endl;	
	cout << "double: 8bytes" << endl;
}

//Takes first int raised to the power of second int
void PrintFirstPowerSecond(int first, int second) {
	cout << "The first number " << first << " raised to the power of the second number " << second << " is : " << pow(first, second) << endl;;  
}

//Prints max between the two numbers
void PrintMaximum(int first, int second) {
	cout << max(first, second) << endl;
}

//Converts number to binary format
void convertToBinary(int number) {
	int remainder;
	if(number <= 1) {
		cout << number;
		return;
	}
	remainder = number % 2;
	convertToBinary(number >> 1);    
	cout << remainder;
}

//Prints the two ints in decimla, octal, hexadecimal, and binary format
void PrintVariousFormats(int first, int second) {
	cout << "Prints the first and second number in decimal format: " << std::dec << first << " " << std::dec << second << endl;
	cout << "Prints the first and second number in octal format: " << std::oct << first << " " << std::oct << second << endl;	
	cout << "Prints the first and second number in hexadecimal format: " << std::hex << first << " " << std::hex << second << endl;
	cout << "Prints the first and second number in binary format: ";
	convertToBinary(first);
	cout << " ";
	convertToBinary(second);
	cout << endl;
}


int main() {
	int first, second, selected;
	cout << "Please enter two positive integers" << endl;
	cin >> first;
	cin >> second;
	//Checks if both numbers are positive
	while(first <= 0 && second <= 0) {
		cout << "Try again. Please enter two positive integers" << endl;
		cin >> first;
		cin >> second;
	}
	cout << "Please select an option from the list" << endl;
	cout << "1. Print out the number of bytes used to store the following data types: bool, char, int, float, and double." << endl;
	cout << "2. Returns the first number raised to the power of the second." << endl;
	cout << "3. Returns the maximum of the two numbers." << endl;
	cout << "4. Prints out the two numbers in decimal, hexadecimal, octal, and binary formats. " << endl;
	cin >> selected;
	//checks if selected valid option
	while(selected > 4 || selected < 1) {
		cout << "Please select another option" << endl;
		cin >> selected;
	}
	cout << endl << "You selected option: " << selected << endl;
	if(selected == 1) {
		PrintBytes();
		cout << endl;
	}
	if(selected == 2) {
		PrintFirstPowerSecond(first, second);
		cout << endl;
	}
	if(selected == 3) {
		PrintMaximum(first, second);
		cout << endl;
	}
	if(selected == 4) {
		PrintVariousFormats(first, second);
		cout << endl;
	}
}
