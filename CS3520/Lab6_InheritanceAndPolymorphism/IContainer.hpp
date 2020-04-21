#ifndef IContainer_h
#define IContainer_h

class IContainer {
    public:
        virtual ~IContainer() {};
        virtual void push_back(const int & element) = 0;
        virtual void push_front(const int & element) = 0;
        virtual void pop_back() = 0;
        virtual void pop_front() = 0;
        virtual int front() const = 0;
        virtual int back() const = 0;
        virtual void insert(int pos, int elem) = 0;
        virtual void erase(int pos) = 0;
        virtual int size() const = 0;
        virtual int get(int pos) const = 0;
};

#endif

