#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream> 
#include "WiimoteAccel.h"

int main()
{
	WiimoteAccel wiimote;
	wiimote.Listen();
}