#include "Furniture.h"

//represents a bed
class Bed : public Furniture {
	private:
		//represents bed size(twin, full, queen, king)
		std::string bedSize;
	public:
		//constructor
		Bed(std::string name, std::string bedSize);
		//prints out bed information
		virtual void Print();
};