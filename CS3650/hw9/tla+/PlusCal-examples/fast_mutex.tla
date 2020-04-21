----------------------- MODULE fast_mutex -------------------------

\*********************************************************************
\* Copied from: https://github.com/quux00/PlusCal-Examples/tree/master/FastMutex
\*          by: Michael Peterson
\* Based on example in "A PlusCal User's Manual, C-syntax"
\* (with slight modifications.)
\* This version of mutual exclusion (mutex) is implemented entirely in
\*   in software, without the need for a hardware test-and-set instruction.
\*
\* BASED ON:
\* Leslie Lamport.  A fast mutual exclusion algorithm.
\* ACM Transactions on Computer Systems , 5(1):1–11, February 1987.
\*********************************************************************

EXTENDS Naturals, TLC
CONSTANT N

(*
--algorithm FastMutex {
  variables x,
            y = 0,
            b = [i \in 1..N |-> FALSE];
  process (Proc \in 1..N)
    variable j;
  {
      ncs: while (TRUE) {
             skip; \* the noncritical section

    start:   b[self] := TRUE;
      s01:   x := self;
       
      s02:   if (y /= 0) {
      s03:     b[self] := FALSE;
      s04:     await y = 0; 
               goto start;
             };
             
      s05:   y := self;
      s06:   if (x /= self) {
      \* Try commenting out: b[self] := FALSE, below.  The result is deadlock.
      s07:     b[self] := FALSE; 
               j := 1;
               
      s08:     while (j <= N) {
      \* In order to patch the s07 change, try: await ~b[j] \/ j = self, below.
      \* The result is deadlock.
                 await ~b[j];
                 \* Try changing to j+2 to see a violation of assertion below.
                 \* We then lose mutual exclusion.
                 j := j+1;
               };
               
      s09:     if (y /= self) {  
      s10:       await y = 0; 
                 goto start;
               };
             };
       
       cs:   assert \A idx \in 1..N : (idx /= self) => (pc[idx] /= "cs");
             skip ; \* The critical section.
      s11:   y := 0;
      s12:   b[self] := FALSE;       
           } \* end outer while
                 
  } \* end process block
} \* end algorithm
*)

================================================
