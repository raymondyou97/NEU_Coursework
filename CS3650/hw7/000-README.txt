			Homework 7
                   DUE:  Fri., Mar. 2

**** NOTE:  If you have a choice for a replacement policy, please use
****        the FIFO ("first in, first out") policy, as specified in this
****        assignment.  It's true that real caches usually use an LRU policy,
****        but that is more complex to implement.

**** NOTE:  A natural way to implement a FIFO policy is with a linked list.
****          See hw7-c-paradigms.txt.
****        Also, see Chapter 17 (Free Space Management) of http://ostep.org

**** A student found these excellent youtube videos by Abelardo Pardo,
**** which describe the cache similarly to my own lecture.  I hope this helps
**** to supplement the chapter in the textbook, which was a little weak for
**** this one topic.
**** > Direct-mapped: https://www.youtube.com/watch?v=bTj0vFs8ndI
**** > Associative: https://www.youtube.com/watch?v=YAz0qJf05ko
**** > Set-Associative: https://www.youtube.com/watch?v=ReKzEGLlGfk
**** > 
**** > It is a good idea to follow them in that order, as the explanations
**** > start with a review from the previous videos.

====
STATIC ANALYSIS (required before submitting your homework):

(See below for assignment.  This assignment requires one more programming tool.)
This assignment introduces one more tool commonly used in Linux.
We have seen  'gcc', 'gdb', 'make', 'vi', 'tar', and 'man'.
We will now use 'clang-check', which is a _static_ analyzer to catch
bugs and style errors _prior_ to execution.
    For this assignment, you will also be required to use the clang
static analysis tool to check the style and structure of your program.
This tool is available on CCIS Linux computers, and here's a general
web site about the tools:
  http://clang-analyzer.llvm.org/
But we will only use the command-line oriented version:  clang-check
And here are some examples of how other people use clang-check:
  http://clang-analyzer.llvm.org/available_checks.html

The grader will be instructed to run clang-check on your program.
If the grader finds that the clang analysis returns a significant
number of flaws (whether of style or potential bugs), then you will
be marked down at least 10 points out of 100.

Here is a simple example on how to use clang-check:
If you would normally type:
  gcc -g -O0 cache-sim.c
then you can check your code by typing:

  clang-check --analyze cache-sim.c -- -g -O0

That's all there is to it.  Then read any clang warnings and fix them.
P.S.: If your command line has no flags, you still need "--":
        clang-check --analyze cache-sim.c --

====
ASSIGNMENT:

In the following, I now describe the requirements for this assignment.

You need to write the cache emulator below, and test it
on the given sequence.  You must write the emulator in
		the C language.
You must also provide a Makefile similar to the one in:
		/course/cs3650/homework/hw4/Makefile
You can then compile and run your program simply by typing `make'.
Before turning it, type `make dist' to produce a gzipped tarball ending
in .tar.gz.  (This is the equivalent in UNIX/Linux for the Windows .zip files.)
Then turn in the .tar.gz file.
(Makefile is like a project file, but it is human-readable text.
 When you type `make', the make command looks in the current directory
 for a file called `Makefile'.  Read the Makefile to see how it works.)

An example is provided in the instructor's directory.
The grader will run your emulator on a new sequence for which
you will not have the answers.  If you are successful on the test cases,
then I expect you will receive 100 for this homework.

Write an emulator for a n-way set associative cache of size s, with blocks or
cache lines of size l (ell).  One possible way to write the emulator
is to accept three parameters:
s, l, and n.  The parameters s and l should be specified in units of bytes.
So, a 128-byte 1-way set associative cache with 8-byte cache lines
(8-byte cache blocks) would have s = 128, l = 8,
and n = 1 (n-way cache, for n=1).  You may also want to allow a fourth
parameter to indicate a special case (direct-mapped or fully associative).

As we will see in class, a  direct-mapped cache corresponds to
a 1-way set associative cache (n=1), and a fully associative corresponds
to a n-way set associative cache with n=s/l, the number of rows (lines) in
the cache.

The cache emulator should accept a sequence of addresses from the CPU, and
determine what the contents of the cache will be after receiving each address.
For simplicity, assume that all addresses are read-only and they request
only one byte of data.  The sequence of
addresses may be input in any manner that you like.  A particularly easy way
is to include in your program initialized C statements such as:
 int test_set_1[] = {44, 56, 13, 24, ...};

For each case, the cache should be initially empty.  Within an associative
set, the data is entered and removed using a FIFO strategy.  Hence, a cache
hit does not affect the FIFO ordering.  (Note that this is not a LRU strategy.
LRU is the ideal strategy, but many real caches use an approximation to LRU,
such as FIFO, that is easier to implement in hardware.)  The output
of your program should be the same sequence of addresses, with each
address followed immediately by the word "HIT" or "MISS" (depending
on whether a cache hit or miss occurs).

Note that the course directory contains a Linux executable, hw7.cache-sim,
which is a working simulator.  You can use this executable on the
CCIS Linux computers to develop tests to check the correctness of your
own code.

You may develop the code anywhere, but you must port it to run on our
Linux system.  On our Linux system, you must also provide a _working_
Makefile, similar to the previous hw4/Makefile.

======================
HAND IN:  hw7

By the due date, you will have to submit these things in your .tar.gz file:
 * Place your source code (e.g. cache.c), a working Makefile,
      an output file (cache.out), and the four test runs:
	 in a subdirectory, hw7
    Then:
      tar cvf hw7.tar ./hw7
      gzip hw7.tar
      submit-cs3650-hw7 hw7.tar.gz
    The submit script tells you where your file was stored.
    Remember the full name.  You can delete it later and resubmit if you like.

======================
One sequence of addresses is to be used for each of the four test runs.
For simplicity, assume all addresses are for a "lb" (load byte) instruction.
The test sequence is:
0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72,
  76, 80, 0, 4, 8, 12, 16, 71, 3, 41, 81, 39, 38, 71, 15, 39, 11, 51, 57, 41

Test Run 1:
Assume a 128-byte, direct-mapped cache with 8-byte cache lines (cache blocks).

Test Run 2:
Assume a 64-byte, 2-way set associative cache with 8-byte cache lines (cache
blocks).

Test Run 3:
Assume a 128-byte, direct-mapped cache with 16-byte cache lines (cache blocks).

Test Run 4:
Assume a 64-byte, fully associative cache with 8-byte cache lines (cache
blocks).
