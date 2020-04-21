#ifndef FURNITURE_H
#define FURNITURE_H

//represents a furniture
class Furniture {
	private:
		//represents the dimensions
		float width, height, depth;
		//represents name of furniture
		std::string name;
	
	public:
		//constructor
		Furniture(std::string name);
		//reads user inputs for dimensions
		void ReadDimensions();
		//prints out furniture information
		virtual void Print();
};

#endif