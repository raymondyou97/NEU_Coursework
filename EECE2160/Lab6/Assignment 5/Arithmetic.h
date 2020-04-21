#ifndef ARITHMETIC1_H
#define ARITHMETIC1_H
// Physical base address of GPIO
const unsigned gpio_address = 0x400d0000;
// Length of memory-mapped IO window
const unsigned gpio_size = 0xff;
const int A_offset = 0x100; // Offset for value A
const int B_offset = 0x104; // Offset for value B
const int code_offset = 0x108; // Offset for the code
const int Y_offset = 0x10c; // Offset for output Y
class Arithmetic
{
// File descriptor for memory-mapped I/O
int fd;
// Mapped address
char *pBase;
public:
// Class constructor
Arithmetic();
// Destructor
~Arithmetic();
// Write a value into the given memory offset in the memory-mapped I/O.
void RegisterWrite(unsigned offset, unsigned value);
// Read a value from the given memory offset in the memory-mapped I/O.
int RegisterRead (unsigned offset);
};
#endif 