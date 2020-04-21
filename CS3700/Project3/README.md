# Project 3

- Simple Transport Protocol
- Team Name: PythonCats
- Team Members: Raymond You, Oliver Zheng

## High Level Approach

We first looked over the starter code given to get a glimpse of how the implementation would look. We decided it would be easier if we just did it from scratch as a lot of the starter code didn't seem necessary and we can just take parts of the starter code that we could use. Next, we decided on the sliding window tcp algorithm to implement for our TCP implementation. We added ACKs, sequence nums, timeouts, and more as they were necessary for our implementation for both the sender and receiver. We then tackled each problem sequentially, packets that are dropped, packets that are out of order, delays in the packets being sent, and duplicate packets being sent. Next, we implemeneted the data structures to keep track of which packets have been sent, which acks have been sent, which acks have been retrieved using mainly maps and lists. We keep track of the packets that have been sent and match it with all the packets that are incoming, to avoid duplicate packets and also see which packets have been failed to be sent. We also kept track of the window and shifted to the right each time we successfully get an ack back from the receiver so we can grab the next set of data. We also played around with all the timeout times to achieve the performance aspect of this assignment.

## Challenges Faced

The main challenges we faced were implementing the sliding window tcp algorithm properly. Everytime we made a change on one end for example the sender, we also needed to make the correct changes on the receiver end. We often found that we would make a slight change on one side and it would break the other end. Thus, we had to work very carefully not to have any regressions everytime we made it to a milestone. Another challenge we faced was what the specific criterias were when resending a packet, considering it a dropped packet. We also had a test that kept timing out so we had to keep tweaking the variables to get optimality. Furthermore, some tests were flakey and we just kept guess and checking by tweaking the values until it eventually seemed stable enough.

## Testing

For testing, we mainly used the logger examples given in the starter code as opposed to the usual print statements used in previous assignments. Everytime, we made a change we would watch and look at the logs outputted to make sure it was intended functionality.
