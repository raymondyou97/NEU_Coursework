#include <iostream>
#include "RoboticArm.h"
#include <unistd.h>
using namespace std;

int main()
{
        RoboticArm robotic_arm;
        int command;
        cout << "Welcome to the Robot Show" << endl;
        cout << "Please select a command" << endl;
        cout << "1. Dance" << endl << "2. Lay down" << endl <<
        "3. Grab an object" << endl << "4. Default positions" << endl;
        cout << "User command 9 whenever to exit the program" << endl << endl;
        cin >> command;
        cout << endl;
        if (command == 9) {
                return 0;
        }
        while(command < 0 || command > 4) {
            cout << "Please select another option" << endl;
            cout << "1. Dance" << endl << "2. Lay down" << endl <<
            "3. Grab an object" << endl << "4. Default positions" << endl;
            cout << "User command 9 whenever to exit the program" << endl << endl;
            cin >> command;
            if (command == 9) {
                return 0;
            }
        }

        while (true) {
            //dance
            while(command == 1) {
                cout << "Enter another command if you want the arm to do something else" << endl;
                cout << "1. Dance" << endl << "2. Lay down" << endl <<
                "3. Grab an object" << endl << "4. Default positions" << endl;
                cout << "User command 9 whenever to exit the program" << endl << endl;
                cin >> command;
                while(command < 0 || command > 4) {
                    cout << "Please select another option" << endl;
                    cout << "1. Dance" << endl << "2. Lay down" << endl <<
                    "3. Grab an object" << endl << "4. Default positions" << endl;
                    cout << "User command 9 whenever to exit the program" << endl << endl;
                    cin >> command;
                    cout << endl;
                    if (command == 9) {
                        cout << "Thank you for attending the robot show. Have a good day" << endl;
                        return 0;
                    }
                }
                cout << endl;
            }
            //lay down
            while(command == 2) {
                cout << "Enter another command if you want the arm to do something else" << endl;
                cout << "1. Dance" << endl << "2. Lay down" << endl <<
                "3. Grab an object" << endl << "4. Default positions" << endl;
                cout << "User command 9 whenever to exit the program" << endl << endl;
                cin >> command;
                while(command < 0 || command > 4) {
                    cout << "Please select another option" << endl;
                    cout << "1. Dance" << endl << "2. Lay down" << endl <<
                    "3. Grab an object" << endl << "4. Default positions" << endl;
                    cout << "User command 9 whenever to exit the program" << endl << endl;
                    cin >> command;
                    cout << endl;
                    if (command == 9) {
                        cout << "Thank you for attending the robot show. Have a good day" << endl;
                        return 0;
                    }
                }
                cout << endl;
            }
            //grab an object
            while(command == 3) {
                robotic_arm.MoveServo(0, 70, 45);
                robotic_arm.MoveServo(1, 30, 45);
                robotic_arm.MoveServo(2, 60, 45);
                robotic_arm.MoveServo(4, 180, 45);
                sleep(3);
                robotic_arm.MoveServo(4, 0, 45);
                sleep(3);
                cout << "Enter another command if you want the arm to do something else" << endl;
                cout << "1. Dance" << endl << "2. Lay down" << endl <<
                "3. Grab an object" << endl << "4. Default positions" << endl;
                cout << "User command 9 whenever to exit the program" << endl << endl;
                cin >> command;
                if (command == 9) {
                    cout << "Thank you for attending the robot show. Have a good day" << endl;
                    return 0;
                }
                while(command < 0 || command > 4) {
                    cout << "Please select another option" << endl;
                    cout << "1. Dance" << endl << "2. Lay down" << endl <<
                    "3. Grab an object" << endl << "4. Default positions" << endl;
                    cout << "User command 9 whenever to exit the program" << endl << endl;
                    cin >> command;
                    cout << endl;
                    if (command == 9) {
                        cout << "Thank you for attending the robot show. Have a good day" << endl;
                        return 0;
                    }
                }
                cout << endl;
            }
            //default positions
            while(command == 4) {
                cout << "Enter another command if you want the arm to do something else" << endl;
                cout << "1. Dance" << endl << "2. Lay down" << endl <<
                "3. Grab an object" << endl << "4. Default positions" << endl;
                cout << "User command 9 whenever to exit the program" << endl << endl;
                cin >> command;
                if (command == 9) {
                    cout << "Thank you for attending the robot show. Have a good day" << endl;
                    return 0;
                }
                while(command < 0 || command > 4) {
                    cout << "Please select another option" << endl;
                    cout << "1. Dance" << endl << "2. Lay down" << endl <<
                    "3. Grab an object" << endl << "4. Default positions" << endl;
                    cout << "User command 9 whenever to exit the program" << endl << endl;
                    cin >> command;
                    cout << endl;
                    if (command == 9) {
                        cout << "Thank you for attending the robot show. Have a good day" << endl;
                        return 0;
                    }
                }
                cout << endl;
            }
            while(command == 9) {
                cout << "Thank you for attending the robot show. Have a good day" << endl;
                return 0;
            }
        }
}
    
