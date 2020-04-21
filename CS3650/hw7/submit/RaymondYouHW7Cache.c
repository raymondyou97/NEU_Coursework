//Raymond You
//CS 3650 - Professor Cooperman
//HW 7

//Had to add -std=c99 in the makefile so that it compiled in mobaxterm. Remove it if it doesn't compile

#include <stdio.h>

//Replace AddressesGiven Array with test set input. Currently has the default values given by professor
const int AddressesGiven[] = {0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 0, 4, 8, 12, 16, 71, 3, 41, 81, 39, 38, 71, 15, 39, 11, 51, 57, 41};

const int AddressesLength = sizeof(AddressesGiven) / 4;
// represents each cache line
//--------------------------------------------
//|			  |					|		     |
//|  valid    |  set(optional)  |    tag     |
//|			  |					|	     	 |
//--------------------------------------------
struct StructCacheLine {
	int tag, set, valid;
};
//represents bits of the cpu address
struct StructAddress{
    int tag, index, offset, address, set;
};
struct StructCacheLine cache[5000];

//---------------------------------------------------------------------------------------------------------------------------
//Direct Mapped Functions

void PrepareDirectMapped(struct StructAddress addressesGiven[], int CacheSize, int BlockSize) {
	int NumberOfLines = CacheSize / BlockSize;
	int TagIndex = 0;
	for(int i = 0; i < AddressesLength; i++) {
		addressesGiven[i].address = AddressesGiven[i];
		TagIndex = AddressesGiven[i] / BlockSize;
		addressesGiven[i].tag = TagIndex / NumberOfLines;
		addressesGiven[i].index = TagIndex % NumberOfLines;
		addressesGiven[i].offset = AddressesGiven[i] % BlockSize;
		//0 for all valid bits
		cache[i].valid = 0;
	}
}

void RunDirectMapped(struct StructAddress addressesGiven[], int NumberOfLines) {
	for(int i = 0; i < AddressesLength; i++) {
		//check if valid bit equal
		if(cache[addressesGiven[i].index].valid == 1) {
			//check if tags equals
			int addressTag = addressesGiven[i].tag;
			int cacheTag = cache[addressesGiven[i].index].tag;
			if(addressTag == cacheTag) {
				// int int int int
			    printf(" %d: HIT (Tag #/Index #/Offset #: %d/%d/%d)\n", AddressesGiven[i], addressesGiven[i].tag, addressesGiven[i].index, addressesGiven[i].offset);
			}
		}
		//else replace cache tag
		else {
			// int int int int
			printf(" %d: MISS (Tag #/Index #/Offset #: %d/%d/%d)\n", AddressesGiven[i], addressesGiven[i].tag, addressesGiven[i].index, addressesGiven[i].offset);
			//set valid bit
			cache[addressesGiven[i].index].valid = 1;
			cache[addressesGiven[i].index].tag = addressesGiven[i].tag;
		}
	}
	//print out contents
	printf("The cache contents are:\n");
	for(int j = 0; j < NumberOfLines; j++)
		if(cache[j].valid) {
			printf("%d: VALID: True; Tag: %d\n", j, cache[j].tag);
		}
		else {
			printf("%d: VALID: False; Tag: -\n", j);
	}
}

//---------------------------------------------------------------------------------------------------------------------------
//Fully Associative Functions

void PrepareFullyAssociative(struct StructAddress addressesGiven[], int CacheSize, int BlockSize, int sets[]) {
	//ex. 50 = 400 / 8
	int NumberOfLines = CacheSize / BlockSize;
	int OffsetValue = 0;
	int TagFinal = 0;
	for(int i = 0; i < AddressesLength; i++) {
		addressesGiven[i].address = AddressesGiven[i];
		OffsetValue = AddressesGiven[i] % BlockSize;
		addressesGiven[i].offset = OffsetValue;
		TagFinal = AddressesGiven[i] / BlockSize;
		addressesGiven[i].tag = TagFinal;
		sets[i] = 0;
	}
	//0 for all valid bits
	for(int i = 0; i < NumberOfLines; i++) {
		cache[i].valid = 0;
	}
}

void RunFullyAssociative(struct StructAddress addressesGiven[], int sets[], int NumberOfLines) {
	//keep track if hit or not
    int HitOrNot = 0;
	//keep track of which is the last one in (LIFO policy)
	// 0 - numLines, then back to 0
	int lastIn = 0;
	//go through given addressesGiven
	for(int i = 0; i < AddressesLength; i++) {
        HitOrNot = 0;
		//try to get a cache hit
 		for(int j = 0; j < NumberOfLines; j++) {
 			if(cache[j].valid == 1) {
				//check tags
				int cacheTag = cache[j].tag;
				int addressTag = addressesGiven[i].tag;
 				if(cacheTag == addressTag) {
					//check sets
					int cacheSetNo = cache[j].set;
					int addressSetNo = sets[i];
					if(cacheSetNo == addressSetNo) {
						HitOrNot = 1;
						break;
					}
 				}
            }
 		}
		//for print output
		char* HitOrMiss;
		if(HitOrNot == 1) {
			HitOrMiss = "HIT";
		}
		else {
			HitOrMiss = "MISS";
		}
		// int char int int int
        printf(" %d: %s (Tag #/Set #/Offset #: %d/%d/%d)\n", addressesGiven[i].address, HitOrMiss, addressesGiven[i].tag, sets[i], addressesGiven[i].offset);

		//if missed
 		if (HitOrNot == 0) {
			int CheckSetFull = 1;
			//check if set is full
			for(int temp = 0; temp < NumberOfLines; temp++) {
				if(cache[temp].valid == 0) {
					int set1 = cache[temp].set;
					int set2 = sets[i];
					if(set1 == set2) {
						CheckSetFull = 0;
					}
				}
			}
            // check if set is full
 			if(CheckSetFull == 1) {
				//replace lastIn line (first in first out policy)
 				cache[lastIn].tag = addressesGiven[i].tag;
 				cache[lastIn].valid = 1;
                //increment index of lastIn cache line
				lastIn++;
				//reached end reset
				if(lastIn == NumberOfLines) {
					lastIn = 0;
				}
				
 			}
            // else place in the set
 			else {
 				for(int x = 0; x < NumberOfLines; x++) {
 					if(cache[x].valid == 0) {
						int set1 = cache[x].set;
						int set2 = sets[i];
						if(set1 == set2) {
							cache[x].tag = addressesGiven[i].tag;
							cache[x].valid = 1;
							break;
						}
					}
				}
			}
		}
	}
	//print out cache lines
	printf("The cache contents are: \n");
	for(int y = 0; y < NumberOfLines; y++) {
		if(cache[y].valid == 1) {
			printf("%d: Valid: True; Tag %d (Set #: %d)\n", y, cache[y].tag, cache[y].set);
		}
		else {
			printf("%d: Valid: False; Tag %d (Set #: %d)\n", y, cache[y].tag, cache[y].set);
		}  
	}
}

//---------------------------------------------------------------------------------------------------------------------------
//N-Associative Functions

//ex. 400, 8, 2
void PrepareNAssociative(struct StructAddress addressesGiven[], int CacheSize, int BlockSize, int SetSize, int sets[]) {
	//number of lines
	int NumberOfLines = CacheSize / BlockSize;
	//number of sets
	int numSets = NumberOfLines / SetSize;
	//size of each set
	int setSize = NumberOfLines / numSets;
	int TagIndex = 0;
	int OffsetValue = 0;
	int TagFinal = 0;
    for(int x = 0; x < AddressesLength; x++) {
		addressesGiven[x].address = AddressesGiven[x];
	    OffsetValue = AddressesGiven[x] % BlockSize;
		addressesGiven[x].offset = OffsetValue;
		TagIndex = AddressesGiven[x] / BlockSize;
		TagFinal = TagIndex / numSets;
		addressesGiven[x].tag = TagFinal;
		sets[x] = TagIndex % numSets;
	}
	//0 for all valid bits initial
	for(int y = 0; y < NumberOfLines; y++) {
		cache[y].valid = 0;
		cache[y].set = y / setSize;
	}
}
//the random comments are reference for myself
//entered 400, 8, 2
//numberoflines = 50
//numsets = 25
//setSize = 2
void RunNAssociative(struct StructAddress addressesGiven[], int sets[], int numSets, int NumberOfLines) {
	//ex. 2 = 50 / 25
	//Lines in each set = 2
	int setSize = NumberOfLines / numSets;
	//represents first of each set in overall all lines
	int FirstIndexEachSet[numSets];
	

	for(int x = 0; x < numSets; x++){
		//0 2 4 6 8...
		FirstIndexEachSet[x] = x * setSize;
    }
	
	
	//represents first line of each set
	int FirstIndexEachSet2[numSets];
	for(int y = 0; y < numSets; y++){
		//0 2 4 6 8..
		FirstIndexEachSet2[y] = FirstIndexEachSet[y];
    }
    int HitOrNot = 0;
	int lastIn = 0;
	for(int i = 0; i < AddressesLength; i++) {
        HitOrNot = 0;
 		lastIn = FirstIndexEachSet[sets[i]];

 		for(int j = 0; j < NumberOfLines; j++) {
			//check if valid bit 1
 			if(cache[j].valid == 1) {
				//check if tags equal
				int cacheTag = cache[j].tag;
				int addressTag = addressesGiven[i].tag;
 				if(cacheTag == addressTag) {
					//check if sets equal
					int cacheSetNo = cache[j].set;
					int addressSetNo = sets[i];
					if(cacheSetNo == addressSetNo) {
						HitOrNot = 1;
						break;
					}
 				}
            }
 		}
        //for print output
		char* HitOrMiss = "";
		if(HitOrNot == 1) {
			HitOrMiss = "HIT";
		}
		else {
			HitOrMiss = "MISS";
		}
		// int char int int int 
        printf(" %d: %s (Tag #/Set #/Offset #: %d/%d/%d)\n", addressesGiven[i].address, HitOrMiss, addressesGiven[i].tag, sets[i], addressesGiven[i].offset);

		//if missed
 		if (HitOrNot == 0) {
			//check if set is full
			int CheckSetFull = 1;
			for(int temp = 0; temp < NumberOfLines; temp++ ) {
				//valid bit 0?
				if(cache[temp].valid == 0) {
					//check if sets equal
					int cacheSetNo = cache[temp].set;
					int addressSetNo = sets[i];
					if(cacheSetNo == addressSetNo) {
						CheckSetFull = 0;
					}
				}
			}
            //if set is full replace..
 			if(CheckSetFull == 1) {
 				cache[lastIn].tag = addressesGiven[i].tag;
 				cache[lastIn].valid = 1;
				//update with LIFO policy
				int temp = setSize + FirstIndexEachSet2[sets[i]] - 1;
				if(temp == lastIn) {
					//set as first line in set
					FirstIndexEachSet[sets[i]] = FirstIndexEachSet2[sets[i]];
				}
				else {
					//increment
					FirstIndexEachSet[sets[i]]++;
				}
                
 			}
            // else place in the set
 			else {
 				for(int j = 0; j < NumberOfLines; j++) {
					//check valid?
 					if(cache[j].valid == 0) {
						//set number equal?
						int set1 = cache[j].set;
						int set2 = sets[i];
						if(set1 == set2) {
							//update cache
							cache[j].tag = addressesGiven[i].tag;
							cache[j].valid = 1;
							break;
						}
 					}
 				}
 			}
 		}
 	}
	//print out all cache lines
	printf("The cache contents are:\n");
	for(int k = 0; k < NumberOfLines; k++) {
		if(cache[k].valid == 1) {
			printf("%d: Valid: True; Tag %d (Set #: %d)\n", k, cache[k].tag, cache[k].set);
		}
		else {
			printf("%d: Valid: False; Tag %d (Set #: %d)\n", k, cache[k].tag, cache[k].set);
		}
	}
}

//---------------------------------------------------------------------------------------------------------------------------


int main() {
	//choose which cache type
    int choice = 12345;
    while (choice == 12345){
        printf("Choose a cache type:\n"
                "0 - direct-mapped\n"
                "1 - n-associative\n"
                "2 - fully associative\n: ");
        scanf("%i", &choice);
		//keep going if invalid input
        if (choice < 0 || choice > 2) {
			printf("Please enter a valid cache type input.");
			choice = 12345;
		}
    }
	//get cache size
	int CacheSize = 0;
    printf("Enter a cache size: \n");
    scanf("%d", &CacheSize);
	//get block size
	int BlockSize = 0;
    printf("Enter a block size: \n");
    scanf("%d", &BlockSize);
	struct StructAddress addressesGiven[AddressesLength];
	
	if(!(choice >= 0 && choice <= 2)) {
		printf("Error");
		return 0;
	}
	//direct
	else if (choice == 0) {
		PrepareDirectMapped(addressesGiven, CacheSize, BlockSize);
		int NumberOfLines = CacheSize / BlockSize;
        RunDirectMapped(addressesGiven, NumberOfLines);
    }
	//N-assoc
    else if (choice == 1) {
		int SetSize = 0;
		//Get set size
        printf("Enter a set size: \n");
        scanf("%d", &SetSize);
		int sets[AddressesLength];
		PrepareNAssociative(addressesGiven, CacheSize, BlockSize, SetSize, sets);
		int NumberOfLines = CacheSize / BlockSize;
		int numSets = NumberOfLines / SetSize;
        RunNAssociative(addressesGiven, sets, numSets, NumberOfLines);
	}
	//Fully Assoc
	else {
		int sets[AddressesLength];
		PrepareFullyAssociative(addressesGiven, CacheSize, BlockSize, sets);
		int NumberOfLines = CacheSize / BlockSize;
        RunFullyAssociative(addressesGiven, sets, NumberOfLines);
	}
	//exit
	return 0;
}
