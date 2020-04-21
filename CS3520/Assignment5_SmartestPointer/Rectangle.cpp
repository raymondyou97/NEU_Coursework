#include "Rectangle.hpp"

#include <string>

Rectangle::Rectangle() : m_id("Unknown") {};

Rectangle::Rectangle(std::string id) : m_id(id) {};

Rectangle::Rectangle(const Rectangle & other) {
    this->m_id = other.m_id + "copy";
}

Rectangle::~Rectangle() {}

std::string Rectangle::getId() {
    return this->m_id;
}

void Rectangle::setId(std::string id) {
    this->m_id = id;
}
