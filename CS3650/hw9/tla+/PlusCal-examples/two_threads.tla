---------------------------- MODULE two_threads ----------------------------
\* Copyright (c) 2017, Gene Cooperman.  May be freely distributed
\* and modified as long as this copyright notice remains.

EXTENDS Naturals, TLC

(*
--algorithm threads {
  variables x=0, y=0;
  
  process (thread1 = "thr1")
  { start1:  skip; \* Do nothing at beginning
    1a: if ( y=0 ) {
    1b:     x:=1; } ;
    end1a: if (pc["thr2"] = "Done") { \* If other guy is done
          print <<"x, y:", x, y>> ;
    end1b:   assert ~(x=1 /\ y=1) ; \* Condition "not(x==1 && y==1)" can fail
        }
  } \* end process block
  
  process (thread2 = "thr2")
  { start2:  skip; \* Do nothing at beginning
    2a: if ( x=0 ) {
    2b:     y:=1; } ;
    end2a: if (pc["thr1"] = "Done") { \* If other guy is done
          print <<"x, y:", x, y>> ;
    end2b:   assert ~(x=1 /\ y=1) ; \* Condition "not(x==1 && y==1)" can fail
        }
  } \* end process block

  } \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == {"thr1"} \cup {"thr2"}

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ pc = [self \in ProcSet |-> CASE self = "thr1" -> "start1"
                                        [] self = "thr2" -> "start2"]

start1 == /\ pc["thr1"] = "start1"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["thr1"] = "1a"]
          /\ UNCHANGED << x, y >>

1a == /\ pc["thr1"] = "1a"
      /\ IF y=0
            THEN /\ pc' = [pc EXCEPT !["thr1"] = "1b"]
            ELSE /\ pc' = [pc EXCEPT !["thr1"] = "end1a"]
      /\ UNCHANGED << x, y >>

1b == /\ pc["thr1"] = "1b"
      /\ x' = 1
      /\ pc' = [pc EXCEPT !["thr1"] = "end1a"]
      /\ y' = y

end1a == /\ pc["thr1"] = "end1a"
         /\ IF pc["thr2"] = "Done"
               THEN /\ PrintT(<<"x, y:", x, y>>)
                    /\ pc' = [pc EXCEPT !["thr1"] = "end1b"]
               ELSE /\ pc' = [pc EXCEPT !["thr1"] = "Done"]
         /\ UNCHANGED << x, y >>

end1b == /\ pc["thr1"] = "end1b"
         /\ Assert(~(x=1 /\ y=1), 
                   "Failure of assertion at line 17, column 14.")
         /\ pc' = [pc EXCEPT !["thr1"] = "Done"]
         /\ UNCHANGED << x, y >>

thread1 == start1 \/ 1a \/ 1b \/ end1a \/ end1b

start2 == /\ pc["thr2"] = "start2"
          /\ TRUE
          /\ pc' = [pc EXCEPT !["thr2"] = "2a"]
          /\ UNCHANGED << x, y >>

2a == /\ pc["thr2"] = "2a"
      /\ IF x=0
            THEN /\ pc' = [pc EXCEPT !["thr2"] = "2b"]
            ELSE /\ pc' = [pc EXCEPT !["thr2"] = "end2a"]
      /\ UNCHANGED << x, y >>

2b == /\ pc["thr2"] = "2b"
      /\ y' = 1
      /\ pc' = [pc EXCEPT !["thr2"] = "end2a"]
      /\ x' = x

end2a == /\ pc["thr2"] = "end2a"
         /\ IF pc["thr1"] = "Done"
               THEN /\ PrintT(<<"x, y:", x, y>>)
                    /\ pc' = [pc EXCEPT !["thr2"] = "end2b"]
               ELSE /\ pc' = [pc EXCEPT !["thr2"] = "Done"]
         /\ UNCHANGED << x, y >>

end2b == /\ pc["thr2"] = "end2b"
         /\ Assert(~(x=1 /\ y=1), 
                   "Failure of assertion at line 27, column 14.")
         /\ pc' = [pc EXCEPT !["thr2"] = "Done"]
         /\ UNCHANGED << x, y >>

thread2 == start2 \/ 2a \/ 2b \/ end2a \/ end2b

Next == thread1 \/ thread2
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

==================================================
