#include <iostream>
#include "Bed.h"

//constructor
Bed::Bed(std::string name, std::string bedSize) : Furniture(name) {
	//checks if it is a legitimate bed size
	if(bedSize == "Twin" || bedSize == "Full" || bedSize == "Queen" || bedSize == "King")
		this->bedSize = bedSize;
	else
		std::cout << "Invalid bed size passed in" << std::endl;
}

//prints out bed information
void Bed::Print() {
	Furniture::Print();
	std::cout << "   " << bedSize << " size" << std::endl;
}
