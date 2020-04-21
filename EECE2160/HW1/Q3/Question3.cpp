#include <iostream>
#include <fstream>
#include <string>
using namespace std;

//Represents car class
class Car {
	private:
	//variables that shouldn't change
	string make;
	string model;
	int year;
	string color;

	//constructor with all variables initialized as default
	public:
	Car() {
		make = "";
		model = "";
		year = 0;
		color = "";
	}
	
	//sets the fields of the car class
	void setFields(string mk, string md, int yr, string cl) {
		this->make = mk;
		this->model = md;
		this->year = yr;
		this->color = cl;
	}
	
	//returns the maker
	string getMake() {
		return make;
	}
	
	//returns the model
	string getModel() {
		return model;
	}
	
	//returns the year
	int getYear() {
		return year;
	}
	
	//returns the color
	string getColor() {
		return color;
	}
};  

//represents car records
class CarRecords {
	private: 
	//variables
	int arraySize;
	ifstream infile;
	Car *cars;
	
	//constructor
	public:
	CarRecords(int size) {
		
		//if size is bigger than 10, just return 10 recorsd
		if(size > 10) {
			this->arraySize = 10;
		}
		//for sizes 0-10
		else if(size >= 0) {
			this->arraySize = size;
		}
		//Negative size
		else {
			//Negative sizes become 0
			cout << "Entered a negative number";
			this->arraySize = 0;
		}
		cars = new Car[arraySize];
		infile.open("CarRecords.txt");
		string make, model, color;
		int year, count = 0;
		char ch;
		//Reads the txt file
		while(count < arraySize) {
			infile >> make >> model >> year >> ch >> color;
			Car temp;
			temp.setFields(make, model, year, color);
			cars[count] = temp;
			count++;
		}
	}
	//destructor
	~CarRecords() {
		delete[] cars;
		infile.close();
	}
	
	//prints the car records
	void printCarRecords () {
		cout << "PRINTING " << arraySize << " RECORDS!" << endl;
		cout << "---------------------" << endl;
		for(int i = 0; i < arraySize; i++) {
			cout << cars[i].getMake() << " " << cars[i].getModel() << " " << cars[i].getYear() << ", "<< cars[i].getColor() << endl;
		}
		cout << endl;
	}
	
	//sorts the records in ascending order based on the make field.
	void sort_cars_by_make() {
		cout << "SORTING RECORDS BY MAKE....." << endl;
		for(int i = 0; i < arraySize - 1; i++)
			for( int j = i + 1; j < arraySize; j++) {
				if(cars[i].getMake() > cars[j].getMake()) {
					Car temp = cars[i];
					cars[i] = cars[j];
					cars[j] = temp;
				}
			}
			cout << endl;
		}

	//sorts the records in descending order based on the year field.
	void sort_cars_by_year() {
		cout << "SORTING RECORDS BY YEAR....." << endl;
		for(int i = 0; i < arraySize - 1; i++)
			for(int j = i + 1; j < arraySize; j++) {
				if(cars[i].getYear() > cars[j].getYear()) {
					Car temp = cars[i];
					cars[i] = cars[j];
					cars[j] = temp;
				}
			}
			cout << endl;
			}
		
	//checks for duplicates and prints them
	void print_duplicates() {
		int count = 0;
		cout << "CHECKING FOR DUPLICATES..." << endl;
		for(int i = 0; i < arraySize - 1; i++)
			for( int j = i + 1; j < arraySize; j++) {
				if(cars[i].getYear() == cars[j].getYear() &&
				cars[i].getMake() == cars[j].getMake() &&
				cars[i].getModel() == cars[j].getModel() &&
				cars[i].getColor() == cars[j].getColor()) {
					cout << cars[i].getMake() << " " << cars[i].getModel() << " " << cars[i].getYear() << ", " << cars[i].getColor() << endl;
					cout << cars[j].getMake() << " " << cars[j].getModel() << " " << cars[j].getYear() << ", " << cars[j].getColor() << endl;
					count++;
				}
			}
			cout << endl;
			if(count == 0) {
				cout << "No duplicates found" << endl;
			}
		}
};

int main() {
	int numRecs;
	cout << "Number of Records to read? " ;
	cout << endl;
	cin >> numRecs;
	CarRecords *cr = new CarRecords(numRecs);
	cout << endl;
	// Print car records
	cr->printCarRecords();
	// Sort by Year
	cr->sort_cars_by_year();
	// Print car records
	cr->printCarRecords();
	// Sort by Make
	cr->sort_cars_by_make();
	// Print car records
	cr->printCarRecords();
	// Check for Duplicates
	cr->print_duplicates();
	delete cr;
} // end main

