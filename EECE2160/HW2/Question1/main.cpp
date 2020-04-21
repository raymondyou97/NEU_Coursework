#include <iostream>
#include <string>
#include "Table.h"
#include "Bed.h"

int main() {
	std::string name, type;
	std::cout << "Creating table..." << std::endl;
	std::cout << "   Enter name: ";
	std::cin >> name;
	std::cout << "   Enter wood type (Pine, Oak): ";
	std::cin >> type;
	Table myTable(name, type);
	myTable.ReadDimensions();
	
	std::cout << "Creating bed..." << std::endl;
	std::cout << "   Enter name: ";
	std::cin >> name;
	std::cout << "   Enter size (Twin, Full, Queen, King): ";
	std::cin >> type;
	Bed myBed(name, type);
	myBed.ReadDimensions();
	
	std::cout << std::endl << "Printing objects ..." << std::endl << std::endl;
	myTable.Print();
	myBed.Print();
	
}