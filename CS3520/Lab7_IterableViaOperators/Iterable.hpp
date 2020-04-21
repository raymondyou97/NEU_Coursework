//
//  Iterable.hpp
//  Iterators_InClas
//
//  Created by Vidoje Mihajlovikj on 2/21/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef Iterable_hpp
#define Iterable_hpp

#include <stdio.h>

class Iterable {
    public:
        virtual int & operator[] ( int index ) = 0;
};


#endif /* Iterable_hpp */
