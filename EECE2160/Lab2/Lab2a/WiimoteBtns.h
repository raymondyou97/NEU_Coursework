class WiimoteBtns {
	private:
		int fd; //used to store the file descriptor associated with file /dev/input/event2, as returned by the open() call in the constructor
	
	public:
		WiimoteBtns();			// Default Constructor
		~WiimoteBtns();			// Destructor
		void Listen();
		void ButtonEvent(int code, int value);
};