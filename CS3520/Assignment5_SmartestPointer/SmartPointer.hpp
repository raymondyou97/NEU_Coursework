#ifndef SmartPointer_hpp
#define SmartPointer_hpp

#include "Rectangle.hpp"
#include <map>

class SmartRectanglePointer{
    private:
        Rectangle * data;
        int * counter;
        static std::map<Rectangle *, int> table;
    public:
        SmartRectanglePointer(Rectangle * ptr );
        SmartRectanglePointer(const SmartRectanglePointer & other);
        Rectangle & operator*();
        Rectangle * operator->();
        ~SmartRectanglePointer();
        void reset(Rectangle * ptr);
};

#endif

