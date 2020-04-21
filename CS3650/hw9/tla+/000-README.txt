 Reading PlusCal Algorithms and Understanding their TLA+-based Error Statements
		by Gene Cooperman

Copyright (c) 2017, Gene Cooperman.
This text may be freely distributed and modified as long as this copyright
notice remains.

In these days of many-core CPUs, writing multi-threaded code is becoming
more and more important.  Unfortunately, guaranteeing that multi-threaded
code is correct is also difficult, even for the experts.  For example,
the double-checked locking pattern (DCLP) for lock-free multi-threaded
programming could not be implemented safely in Java until 2004, and
could not be implemented safely in C++ until C++11.  This meant that
there were many legacy implementations of such code in Java and C++11
that were simply incorrect.

Formal verification could have found bugs in those implementations.
But formal verification has traditionally been considered difficult,
and requiring substantial advanced training.  So, developers checked
their multi-threaded code by eye, and hoped that there were no
rare race conditions (perhaps causing a bug only one time in a million).

The PlusCal language is an attempt to make formal verification easily
accessible.  Please note the PlusCal-examples subdirectory.  PlusCal
provides a gentler introduction to the TLA+ toolbox that allows you to
write an algorithm in a format very close to your original source code.

TLA+ is a tool for explicit-state model checking.  The idea is that
you will re-write your original program in a form that plusCal can read.
It is also crucial to add enough labels.  The plusCal system will
view each labeled statement (including all statements until the
next label) as a single atomic statement.  (These labels also serve
a second person.  They will act as our "line numbers" in referring to
both your plusCal program and to the translated TLA+ program
that is created in the same .tla file.)

You choose the level of granularity of your PlusCal model.  You decide
what set of statements act atomically (are found betwee labels),
and TLA+ will then report the results of all possible interleavings
of those atomic statements as multiple threads (called process here) execute.
For example, compare:
  PlusCal-examples/bank_account.tla
  PlusCal-examples/bank_account-assembly.tla
to see the classical bank account example for multi-threading, presented
first at the C source code level, where no bug exists, and then
at the assembly level, where a bad interleaving of assembly instructions
produces a bug.

Let us now begin a reading knowledge-only examination of TLA+ and PlusCal.
For a first look at TLA+, I suggest to ignore all the reference
materials, and simply read carefully:
		PlusCal-examples/two_threads.tla .
If you prefer pretty-printing, you can look instead at a pretty-printed
version of the same source code:
		PlusCal-examples/two_threads.pdf

Note that the code appears near the top in an "--algorithm threads" statement.
This region holds the plusCal version of the code.  The TLA+ toolbox
allows you to translate that into direct TLA+ code.  Note the TLA+
translation appearing after "BEGIN TRANSLATION", lower down in the file.

Presumably, you have already written your multi-threaded code in C or
a similar language.  So, why is it useful to write your code a second
time, but this time in PlusCal, and now with the addition of labels to
indicate which sequences of statements are atomic?  The reason is that
the TLA+ toolbox is an explicit-state model checker.

The model checker allows you to consider _all_ possible inter-leavings
of statements (with some caveats) in the different processes of your
PlusCal program.  Your original multi-threaded program can only select the
random inter-leavings of different threads chosen by the scheduler or your
operating system.  So, now you examine your code from a new viewpoint.

The risk of model checking is that your model may or may not accurately
reflect the original multi-threaded code.  Note the famous aphorism:

	"All models are wrong but some are useful".
    by George Box, in _Robustness in Statistics_, Academic Press, 1979

Now, let's look at the low-level TLA+ code that starts with
"BEGIN TRANSLATION".  Here, your plusCal program has been translated
into a language for explicit-state model checking.  Luckily, with a few
simple clues, this low-level TLA+ language is also easy to read.

The first clue to reading TLA+ is that TLA+ tries to create a model based on
a finite state automaton.  Each state consists of:
  the current statement of each thread (indicated by the PlusCal label); and
  the values of the global variables.  See the TLA+ "VARIABLES" statement.

If your model allows an infinite number of variable values, then you
will have an infinite number of states to check.  So, your model
should restrict the variable values.  For example, maybe all
integer values larger than 3 could be represented by "LARGE".

The second clue to reading TLA+ is that each paragraph typically
refers to a transition between two states.  That is why it will refer
to both pc and pc'.  (Continue reading below for the meaning of pc and pc'.)

The third clue to reading TLA+ is that it refers to a pc[] array.
This is the "program counter".  So, pc["thr1"] refers to the
the current program counter, or statement label for process "thr1".

The fourth clue to reading TLA+ is that a prime (') after a variable
name, such as x', means that this is the value of the the variable
x in the next state (the target of the current transition between states).
Similarly, pc' refers to the value of the program counter in the
next state (i.e., the label of the statement that we will execute
next after the current transition).

The fifth clue to reading TLA+ is that the "=" operator is the same
as "==" in Java or C/C++.  Still More important, no variable is ever
modified or set to a new value in TLA+!  Instead, we are simply comparing
the variable values found in the source and target states, during a
transition between the two states.

Finally, for good or bad, you must get used to reading TLA+ code if
you want to understand what your PlusCal program is doing.  When TLA+
"compiles" a PlusCal program to TLA+, and when TLA+ runs the resulting
TLA+ program within a "model" (analogous to an executable), then any
TLA+ error statements will likely refer to the underlying TLA+ code,
and not to the PlusCal code itself.  TLA+ will provide an error trace
of a series of states if a model error is found.  But that error trace
will refer to TLA+, and not to PlusCal.

The program, two_threads.tla, is a good place to start reading
PlusCal/TLA+.  But when you understand it, consider reading some of the
other PlusCal examples in the same directory.
