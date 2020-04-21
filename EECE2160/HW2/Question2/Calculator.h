#ifndef CALCULATOR_H
#define CALCULATOR_H


//represents template class for a calculator
template<class T>
class Calculator {
	private:
	T value1; //represents first value
	T value2; //represents second value
	public:
	Calculator() {value1 = T(); value2 = T();} //constructior: initializes values to default
	Calculator(T value1, T value2); //constructor: set values 
	T getValue1(); //returns value1
	T getValue2(); //returns value2
	T getSum(); //uses arithmetic operatior '+'
	int getLogicalAND(); //uses logical operatior '&&'
	bool isGreater(); //uses relational operatior '>'
	
};

#endif