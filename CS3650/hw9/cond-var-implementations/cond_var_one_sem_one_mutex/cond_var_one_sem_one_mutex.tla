---------------------------- MODULE cond_var_one_sem_one_mutex ----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT N
(*
--algorithm threads {
  variables total = 0, lock = 0, count = 0, numWaiting = 0, 
    iterations = [i \in  {"thr1", "thr2"} |-> N];
  
  procedure mutex_lock()
  {
    l0: while (TRUE) {
    l1:   if (lock = 0) { \* Test if someone released the lock, or if lock = 0 before
            lock := 1;    \* We atomically test and acquire the lock, and return
    l_end:  return;
          }
        }
  }

  procedure mutex_unlock()
  {
    u0: assert lock = 1;
        lock := 0; \* Release the lock, atomically
    u_end:    return;
  }
  
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
    p0: if(count < 1) {
            count := count + 1;
        };
    p1: return;
  }
  
  
  procedure wait() {
     w1: call mutex_unlock();
     w2: call sem_wait();
     w3: call mutex_lock();
  }
  
  procedure signal() {
     s1: call sem_post();
  }
  
  process (temp \in {"thr1", "thr2"}) { 
    start: while (iterations[self] > 0) {
    p1: if (count = 0) {
    p2:     call signal();
        };
    p3: if (count = 1) {
    p4:     call wait(); 
        };
    };
    assert iterations[self] = 0;
} \* end process block
  

  } \* end algorithm
*)
\* BEGIN TRANSLATION
\* Label w1 of procedure sem_wait at line 29 col 9 changed to w1_
\* Label w2 of procedure sem_wait at line 30 col 11 changed to w2_
\* Label p1 of procedure sem_post at line 42 col 9 changed to p1_
VARIABLES total, lock, count, numWaiting, iterations, pc, stack

vars == << total, lock, count, numWaiting, iterations, pc, stack >>

ProcSet == ({"thr1", "thr2"})

Init == (* Global variables *)
        /\ total = 0
        /\ lock = 0
        /\ count = 0
        /\ numWaiting = 0
        /\ iterations = [i \in  {"thr1", "thr2"} |-> N]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

l0(self) == /\ pc[self] = "l0"
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations, stack >>

l1(self) == /\ pc[self] = "l1"
            /\ IF lock = 0
                  THEN /\ lock' = 1
                       /\ pc' = [pc EXCEPT ![self] = "l_end"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l0"]
                       /\ lock' = lock
            /\ UNCHANGED << total, count, numWaiting, iterations, stack >>

l_end(self) == /\ pc[self] = "l_end"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

mutex_lock(self) == l0(self) \/ l1(self) \/ l_end(self)

u0(self) == /\ pc[self] = "u0"
            /\ Assert(lock = 1, "Failure of assertion at line 21, column 9.")
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "u_end"]
            /\ UNCHANGED << total, count, numWaiting, iterations, stack >>

u_end(self) == /\ pc[self] = "u_end"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

mutex_unlock(self) == u0(self) \/ u_end(self)

w0(self) == /\ pc[self] = "w0"
            /\ count' = count - 1
            /\ pc' = [pc EXCEPT ![self] = "w1_"]
            /\ UNCHANGED << total, lock, numWaiting, iterations, stack >>

w1_(self) == /\ pc[self] = "w1_"
             /\ pc' = [pc EXCEPT ![self] = "w2_"]
             /\ UNCHANGED << total, lock, count, numWaiting, iterations, stack >>

w2_(self) == /\ pc[self] = "w2_"
             /\ IF count > 0
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "w1_"]
                        /\ stack' = stack
             /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

w_iswaiting(self) == /\ pc[self] = "w_iswaiting"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "w1_"]
                     /\ UNCHANGED << total, lock, count, numWaiting, 
                                     iterations, stack >>

sem_wait(self) == w0(self) \/ w1_(self) \/ w2_(self) \/ w_iswaiting(self)

p0(self) == /\ pc[self] = "p0"
            /\ IF count < 1
                  THEN /\ count' = count + 1
                  ELSE /\ TRUE
                       /\ count' = count
            /\ pc' = [pc EXCEPT ![self] = "p1_"]
            /\ UNCHANGED << total, lock, numWaiting, iterations, stack >>

p1_(self) == /\ pc[self] = "p1_"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

sem_post(self) == p0(self) \/ p1_(self)

w1(self) == /\ pc[self] = "w1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_unlock",
                                                     pc        |->  "w2" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "u0"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

w2(self) == /\ pc[self] = "w2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sem_wait",
                                                     pc        |->  "w3" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "w0"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

w3(self) == /\ pc[self] = "w3"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_lock",
                                                     pc        |->  "Error" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

wait(self) == w1(self) \/ w2(self) \/ w3(self)

s1(self) == /\ pc[self] = "s1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sem_post",
                                                     pc        |->  "Error" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

signal(self) == s1(self)

start(self) == /\ pc[self] = "start"
               /\ IF iterations[self] > 0
                     THEN /\ pc' = [pc EXCEPT ![self] = "p1"]
                     ELSE /\ Assert(iterations[self] = 0, 
                                    "Failure of assertion at line 65, column 5.")
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << total, lock, count, numWaiting, iterations, 
                               stack >>

p1(self) == /\ pc[self] = "p1"
            /\ IF count = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations, stack >>

p2(self) == /\ pc[self] = "p2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "signal",
                                                     pc        |->  "p3" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

p3(self) == /\ pc[self] = "p3"
            /\ IF count = 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "p4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations, stack >>

p4(self) == /\ pc[self] = "p4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                     pc        |->  "start" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << total, lock, count, numWaiting, iterations >>

temp(self) == start(self) \/ p1(self) \/ p2(self) \/ p3(self) \/ p4(self)

Next == (\E self \in ProcSet:  \/ mutex_lock(self) \/ mutex_unlock(self)
                               \/ sem_wait(self) \/ sem_post(self)
                               \/ wait(self) \/ signal(self))
           \/ (\E self \in {"thr1", "thr2"}: temp(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


======================================================
