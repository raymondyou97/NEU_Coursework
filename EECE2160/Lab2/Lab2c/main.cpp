#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream> 
#include <cmath>
#include "WiimoteAccel.h"
#include "ZedBoardLeds.cpp"

class WiimoteToLed: public WiimoteAccel {

private:
        ZedBoard *zb;

public:
       WiimoteToLed(ZedBoard * zedboard) {
            this->zb = zedboard;
       }

       void AccelerationEvent(int code, short acceleration) {
            if(code != 3)
                    return;
            if(acceleration > 100)
				acceleration = 100;
            if(acceleration < -100)
				acceleration = -100;
			acceleration = pow(2, (acceleration / 25) + 4);
            zb->WriteAllLeds(acceleration);
       }
};


int main()
{
 // Instantiate ZedBoard object statically
 ZedBoard zed_board;

 // Instantiate WiimoteToLed object statically, passing a pointer to the
 // recently created ZedBoard object.
 WiimoteToLed wiimote_to_led(&zed_board);

 // Enter infinite loop listening to events. The overridden function
 // WiimoteToLed::AccelerationEvent() will be invoked when the user moves
 // the Wiimote.
 wiimote_to_led.Listen();

 // Unreachable code, previous function has an infinite loop
 return 0; 
}