#include "Arithmetic.h"
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>
#include <iostream>
/**
* Constructor Initialize general-purpose I/O
* - Opens access to physical memory /dev/mem
* - Maps memory at offset 'gpio_address' into virtual address space
*
* @param None Default constructor does not need arguments.
* @return None Default constructor does not return anything.
*/
Arithmetic::Arithmetic()
{
// Open memory mapped I/O
fd = open("/dev/mem", O_RDWR);
// Map physical memory
pBase = (char *) mmap(NULL, gpio_size, PROT_READ | PROT_WRITE,
MAP_SHARED, fd, gpio_address);
// Check success
if (pBase == (void *) -1)
{
std::cerr << "Error mapping memory - fogot sudo?\n";
exit(1);
}
}
/**
* Destructor to close general-purpose I/O.
* - Uses virtual address where I/O was mapped.
* - Uses file descriptor previously returned by 'open'.
*
* @param None Destructor does not need arguments.
* @return None Destructor does not return anything.
*/
Arithmetic::~Arithmetic()
{
munmap(pBase, 0xff); // Unmap physical memory
close(fd); // Close memory mapped I/O
}
/**
* Write a 4-byte value at the specified general-purpose I/O location.
*
* - Uses base address returned by 'mmap'.
* @parem offset Offset where device is mapped.
* @param value Value to be written.
*/
void Arithmetic::RegisterWrite(unsigned offset, unsigned value)
{
* (volatile unsigned *) (pBase + offset) = value;
}

/**
* Read a 4-byte value from the specified general-purpose I/O location.
*
* - Uses base address returned by 'mmap'.
* @param offset Offset where device is mapped.
* @return Value read.
*/
int Arithmetic::RegisterRead (unsigned offset)
{
return * (volatile unsigned *) (pBase + offset);
} 