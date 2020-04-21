#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream>
#include "WiimoteBtns.h" 

WiimoteBtns::WiimoteBtns() {
	fd = open("/dev/input/event2", O_RDONLY);
	if (fd == -1)
	{
		std::cerr << "Error: Could not open event file - forgot sudo?\n";
		exit(1);
	} 
}

WiimoteBtns::~WiimoteBtns() {
	// Close Wiimote event file
	close(fd);
}

void WiimoteBtns::Listen() {
	while(true) {
		// Read a packet of 32 bytes from Wiimote
		char buffer[32];
		read(fd, buffer, 32);

		// Extract code (byte 10) and value (byte 12) from packet
		int code = buffer[10];
		int value = buffer[12];
	
		ButtonEvent(code, value);
	}
}

void WiimoteBtns::ButtonEvent(int code, int value) {
	//Print them
	std::cout << "Code = " << code << ", value = " << value << '\n';
}