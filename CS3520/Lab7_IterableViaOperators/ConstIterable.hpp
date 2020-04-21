//
//  ConstIterable.hpp
//  Iterators_InClas
//
//  Created by Vidoje Mihajlovikj on 2/21/20.
//  Copyright © 2020 Vidoje Mihajlovikj. All rights reserved.
//

#ifndef ConstIterable_hpp
#define ConstIterable_hpp

#include <stdio.h>

class ConstIterable {
    public:
        virtual const int & operator[] ( int index ) const = 0;
};

#endif /* ConstIterable_hpp */
