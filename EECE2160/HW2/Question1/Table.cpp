#include <iostream>
#include "Table.h"

//Constructor
Table::Table(std::string name, std::string woodType) : Furniture(name) {
	//checks if it is a woodtype of pine or oak
	if(woodType == "Pine" || woodType == "Oak")
		this->woodType = woodType;
	else
		std::cout << "Invalid wood type passed in" << std::endl;
}

//Prints out table information
void Table::Print() {
	Furniture::Print();
	std::cout << "   " << woodType << " wood" << std::endl;
}
