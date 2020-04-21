#include <iostream>
#include "Furniture.h"

//constructor
Furniture::Furniture(std::string name) {
	this->name = name;
}

//reads user input for dimensions. Dimensions must be greater than 0
void Furniture::ReadDimensions() {
	int width = -1, height = -1, depth = -1;
	while(width < 0) {
		std::cout << "   Enter width: ";
		std::cin >> width;
		if(width < 0)
			std::cout << "Width less than 0. Please enter another number" << std::endl;
	}
	while(height < 0) {
		std::cout << "   Enter height: ";
		std::cin >> height;
		if(height < 0)
			std::cout << "height less than 0. Please enter another number" << std::endl;
	}
	while(depth < 0) {
		std::cout << "   Enter depth: ";
		std::cin >> depth;
		if(depth < 0)
			std::cout << "depth less than 0. Please enter another number" << std::endl;
	}
	this->height = height;
	this->width = width;
	this->depth = depth;
}

//prints out Furniture information such as name, width, height, depth
void Furniture::Print() {
	std::cout << name << ":" << std::endl << "   Width = " << width << ", height = " << height 
	<< ", depth = " << depth << std::endl;
}
