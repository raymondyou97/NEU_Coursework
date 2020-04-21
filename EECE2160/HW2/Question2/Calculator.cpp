#include "Calculator.h"

//constructor that sets values
template<class T>
Calculator<T>::Calculator(T value1, T value2) {
	this->value1 = value1; //sets value1
	this->value2 = value2; //sets value2
}

template<class T>
T Calculator<T>::getValue1() {
	return value1; //returns value1
}

template<class T>
T Calculator<T>::getValue2() {
	return value2; //returns value2
}

template<class T>
T Calculator<T>::getSum() {
	return value1 + value2; //returns sum of value1 and value2
}

template<class T>
int Calculator<T>::getLogicalAND() {
	return value1 && value2; //reurns && of value1 and value2
}

template<class T>
bool Calculator<T>::isGreater() {
	return value1 > value2; //returns > of value1 and value2
}