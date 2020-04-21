class WiimoteAccel {
	private:
		int fd; //used to store the file descriptor associated with file /dev/input/event2, as returned by the open() call in the constructor
	
	public:
		WiimoteAccel();			// Default Constructor
		~WiimoteAccel();			// Destructor
		void Listen();
		virtual void AccelerationEvent(int code, short value);
};