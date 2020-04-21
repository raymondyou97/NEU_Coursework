The codes in this directory are all intended purely as pseudo-code.

Your job is to translate each implementation into a PlusCal file.
Then, after running PlusCal on it, decide it the pseudo-code implements
pthread_cond_wait() and pthread_cond_signal() correctly, or incorrectly.
If the implementation is incorrect, then explain why it is incorrect.

For each file, FILE.code, in this directory, you will need to submit:
  FILE.code
  FILE.tla+  [ Your PlusCal program, including the result
               of running "Translate PlusCal Algorithm" in TLA+.
               Note that you will have to define semaphore and mutex
               in TLA+ as appropriate atomic functions.  You will also
               need to add your own 'process' command or commands (one for
               each thread that you will use in your model).
               Finally, you will also need to add some assert statement
               to check the intended result. ]
  FILE.error-trace [ Only needed if you find an error in the algorithm;
                     This must be a minimum length error-trace from TLA+.
                     Minimize the number of threads and the number of labels
                       in your .tla+ file to the minimum possible, while
                       still producing an error.  Also, minimize any relevant
                       constants such as, maybe, "N" (number of iterations).
                     When you're done, FILE.error-trace should be a copy of:
                       "FILE.toolbox/Model_1/MC_TE.out" (assuming that you're
                       looking at the "Model_1" executable for the
                       "FILE.tla" source code) ]
  FILE.txt   [ Your analysis if the algorithm is correct or incorrect,
               and if it is incorrect, then why.  If it is incorrect, your
               explanation should refer back to specific error frames numbers
               ("STATE (num=XX)") from FILE.error-trace in your explanation. ]

As usual, you should bundle the files in a .tar.gz "tarball", and submit
the .tar.gz file.
