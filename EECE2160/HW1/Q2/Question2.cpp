#include <iostream>
using namespace std;

//rows of matrix
const int rows = 3;
//columns of matrix
const int cols = 3;
//3 by 3 matrix
int matrix[3][3];
//3 by 3 temp matrix used for indexTranpose
int tempMatrix[3][3];

//prints the matrix
void printMatrix(int matrix[rows][cols]) {
	cout << "Your matrix is: " << endl;
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			cout << matrix[i][j] << "      ";
		}
		cout << endl;;
	}
}

//tranposes the array using the indexes
void indexTranpose(int matrix[rows][cols]) {
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			tempMatrix[i][j] = matrix[j][i];
		}
	}
	printMatrix(tempMatrix);
}

//tranposes the array using pointers
void pointerTranspose(int matrix[rows][cols]) {
    int *startingAddress = &matrix[0][0];
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < i; j++) {
            int *first = startingAddress + (i * 3 + j);
            int *second = startingAddress + (j * 3 + i);
			//cout << "-------------------" << endl;
			//cout << *first << "       " << *second << endl;
			//cout << "-------------------" << endl;
            int temp = *first;
            *first = *second;
            *second = temp;
        }
    }
	printMatrix(matrix);
}

int main() {
	//Enters value for the 3 x 3 matrix
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			cout << "Enter a value for Row " << i + 1 << " Col " << j + 1 << ": ";
			cin >> matrix[i][j];
		}
	}
	//Menu where you pick what you want
	cout << "1 to print the matrix \n2 to tranpose using array indices then print \n3 to transpose using pointers then print \n";
	int choice = 0;
	while(choice < 1 || choice > 3) {
		cin >> choice;
		if(choice == 1)
			printMatrix(matrix);
		if(choice == 2) {
			printMatrix(matrix);
			cout << endl << "Tranposing using array indices" << endl;
			indexTranpose(matrix);
		}
		if(choice == 3) {
			printMatrix(matrix);
			cout << endl << "Tranposing using pointers" << endl;
			pointerTranspose(matrix);
		}
	}
}