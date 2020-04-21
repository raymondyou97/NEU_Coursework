#include "Furniture.h"

//represents a table
class Table : public Furniture {
	private:
		//represents the type of wood
		std::string woodType;
	public:
		//constructor takes in a name and the type of wood
		Table(std::string name, std::string woodType);
		//prints out the table information
		virtual void Print();
};