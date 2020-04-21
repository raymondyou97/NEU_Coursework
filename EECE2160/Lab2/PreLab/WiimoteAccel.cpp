#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream> 

class WiimoteAccel {
	private:
	// Open Wiimote event file 
	int fd;
	public:
	WiimoteAccel() {
		fd = open("/dev/input/event0", O_RDONLY);
		if (fd == -1)
		{
			std::cerr << "Error: Could not open event file - forgot sudo?\n";
			exit(1);
		}
	}
	~WiimoteAccel() {
		close(fd);
	}
	void Listen() {
		while (true)
		{
			// Read a packet of 16 bytes from Wiimote
			char buffer[16];
			read(fd, buffer, 16);

			// Extract code (byte 10) and value (byte 12) from packet
			int code = buffer[10];
			short acceleration = * (short *) (buffer + 12);
			ButtonEvent(code, acceleration);
		} 
	}
	void ButtonEvent(int code, int acceleration) {
		  // Print them
		  std::cout << "Code = " << code << ", acceleration = " << acceleration << '\n';
	}
};

int main() {
	WiimoteAccel *accel = new WiimoteAccel();
	accel->Listen();
}