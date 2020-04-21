---------------------------- MODULE semaphore ----------------------------
\* Copyright (c) 2018, Gene Cooperman.  May be freely distributed
\* and modified as long as this copyright notice remains.

EXTENDS Naturals, Sequences, TLC  \* Sequences required for "procedure" stmt
CONSTANT N \* N is number of iterations.  Assign to it in model overview.

(*
--algorithm semaphore {
  variables total = 0, count = 0;

  procedure sem_wait()
  {
    w0: count := count - 1;
    w1: while (TRUE) {
    w2:   if (count > 0) { \* if count > 0 before, or if someone posted to us
            return;
    w_iswaiting: skip;
          }
        }
  }

  procedure sem_post()
  {
    p0: count := count + 1;
    p1: return;
  }
    
  process (thread \in {"thr1", "thr2"})
    variable iterations = N;
  { start: while (iterations > 0) {
      proc1: with (choice \in {1, 2})
               if (choice = 1) {
                 call sem_wait(); }
               else {call sem_post(); };
      proc2: iterations := iterations - 1;
     };
     assert iterations = 0;
  } \* end process block

  process (thread3 = "cleanup")
  { start_cleanup: while (pc["thr1"] /= "Done" \/ pc["thr2"] /= "Done") {
      clean1:        await pc["thr1"] = "Done" \/ pc["thr1"] = "w_iswaiting";
                     if (pc["thr1"] = "w_iswaiting") {
                       call sem_post();
                     };
      clean2:        await pc["thr2"] = "Done" \/ pc["thr2"] = "w_iswaiting";
                     if (pc["thr2"] = "w_iswaiting") {
                       call sem_post();
                     };
      } \* end while
  } \* end process block

} \* end algorithm
*)

====================
