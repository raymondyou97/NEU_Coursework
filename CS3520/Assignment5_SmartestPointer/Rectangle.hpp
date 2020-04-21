#ifndef RECTANGLE_H
#define RECTANGLE_H

#include <string>

class Rectangle {
	private:
        std::string m_id;
    public:
        Rectangle();
        Rectangle(std::string id);
        Rectangle(const Rectangle & other);
        ~Rectangle();
        std::string getId();
        void setId(std::string id);
};

#endif
