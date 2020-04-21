#include <iostream>
#include <string>
#include "Calculator.cpp"
using namespace std;

//represents arithmetic class
class Arithmetic {
	private:
	int intData; //for ints
	float floatData; //for floats
	double doubleData; //for doubles
	template<typename T2>
	/*
	a template function local to this class. The function can be
	called with different types of Calculator objects, and it prints out the values and calls
	getSum(), getLogicalAND(), and isGreater() functions from the template class
	to test the 3 different types of operations, and print the results from those operations as seen
	in the sample output below
	*/
	void printOperations(T2 obj);
	
	public:
	Arithmetic() {intData = 0; floatData = 0; doubleData = 0;} //constructor: initializes all variables to 0
	Arithmetic(int i, float f, double d); //constructor: sets variables
	/*
	– creates a Calculator object of type int from the
	Calculator template class while setting the Calculator values to the local intData and the
	intData from the received object obj. It then calls printOperations(T2 obj)
	function with the newly created Calculator object to test the 3 different types of operations.
	*/
	void intOperations(Arithmetic obj);
	/*
	creates a Calculator object of type float from the
	Calculator template class while setting the Calculator values to the local floatData and
	the floatData from the received object obj. It then calls printOperations(T2 obj)
	function with the newly created Calculator object to test the 3 different types of operations.
	*/
	void floatOperations(Arithmetic obj);
	/*
	creates a Calculator object of type double from
	the Calculator template class while setting the Calculator values to the local doubleData
	and the doubleData from the received object obj. It then calls printOperations(T2
	obj) function with the newly created Calculator object to test the 3 different types of
	operations.
	*/
	void doubleOperations(Arithmetic obj);
	int returnInt(); //helper to return int
	float returnFloat(); //helper to return float
	double returnDouble(); //helper to return double
};

//sets variables of intData, floatData, and doubleData
Arithmetic::Arithmetic(int i, float f, double d) {
	this->intData = i;
	this->floatData = f;
	this->doubleData = d;
}

template<typename T2>
void Arithmetic::printOperations(T2 obj) {
	//line for sum
	cout << obj.getValue1() << " + " << obj.getValue2() << " = " << obj.getSum() << endl;
	//line for &&
	cout << obj.getValue1() << " && " << obj.getValue2() << " = " << obj.getLogicalAND() << endl;
	//because in sample output they wanted true and false instead of 1 and 0 which c++ automatically converts bools to
	string boolean;
	if(obj.isGreater() == 1)
		boolean = "true";
	else
		boolean = "false";
	//line for >
	cout << obj.getValue1() << " > " << obj.getValue2() << " = " << boolean << endl;
}

//returns intData
int Arithmetic::returnInt() {
	return intData;
}

//returns floatData
float Arithmetic::returnFloat() {
	return floatData;
}

//returns doubleData
double Arithmetic::returnDouble() {
	return doubleData;
}

void Arithmetic::intOperations(Arithmetic obj) {
	int temp = obj.returnInt();
	Calculator<int> calculator(intData, temp); //creates calculator object with both int values
	printOperations(calculator); //performs the operations with the ints
}

void Arithmetic::floatOperations(Arithmetic obj) {
	float temp = obj.returnFloat();
	Calculator<float> calculator(floatData, temp); //creates calculator object with both float values
	printOperations(calculator); //performs the operations with the floats
}

void Arithmetic::doubleOperations(Arithmetic obj) {
	double temp = obj.returnDouble();
	Calculator<double> calculator(doubleData, temp); //creates calculator object with both double value
	printOperations(calculator); //performs the operation with the doubles
}

int main() {
	// Create 1st object
	int int1 = 4;
	float f1 = 10.4;
	double d1 = 20.1;
	Arithmetic object1(int1, f1, d1);
	
	// Create 2nd object
	int int2 = 7;
	float f2 = 0.0;
	double d2 = 3.5;
	Arithmetic object2(int2, f2, d2);
	
	// Check operation on integer data type
	cout << "\nPrinting INTEGER operations..." << endl;
	object1.intOperations(object2);
	
	// Check operation on float data type
	cout << "\nPrinting FLOAT operations..." << endl;
	object1.floatOperations(object2);
	
	// Check operation on double data type
	cout << "\nPrinting DOUBLE operations..." << endl;
	object1.doubleOperations(object2);
} // end main 
