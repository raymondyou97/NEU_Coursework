---------------------------- MODULE cond_var_two_sem_one_mutex ----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT N
(*
--algorithm threads {
  variables total = 0, lock = 0, s_count = 0, x_count = 1, waiters = 0,
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
  
  procedure s_semwait()
  {
    s0: s_count := s_count - 1;
    s1: while (TRUE) {
    s2:   if (s_count > 0) { \* if count > 0 before, or if someone posted to us
            return;
    s_iswaiting: skip;
          }
        }
  }

  procedure s_sempost()
  {
    p0: if(s_count < 1) {
            s_count := s_count + 1;
        };
    p1: return;
  }
  
  procedure x_semwait()
  {
    w0: x_count := x_count - 1;
    w1: while (TRUE) {
    w2:   if (x_count > 0) { \* if count > 0 before, or if someone posted to us
            return;
    w_iswaiting: skip;
          }
        }
  }

  procedure x_sempost()
  {
    p0: if(x_count < 1) {
            x_count := x_count + 1;
        };
    p1: return;
  }
  
  
  procedure wait() {
     w1: call x_semwait();
     w2: waiters := waiters + 1;
     w3: call x_sempost();
     w4: call mutex_unlock();
     w5: call s_semwait();
     w6: call mutex_lock();
  }
  
  procedure signal() {
     s1: call x_semwait();
     s2: if(waiters > 0) {
            waiters := waiters - 1;
            call s_sempost();
         };
     s4: call x_sempost();
  }
  
  process (temp \in {"thr1", "thr2"}) { 
    start: while (iterations[self] > 0) {
    p1: if (s_count = 0 \/ x_count = 0) {
    p2:     call signal();
        };
    p3: if (s_count = 1 \/ s_count = 1) {
    p4:     call wait(); 
        };
    };
    assert iterations[self] = 0;
} \* end process block
  

  } \* end algorithm
*)
\* BEGIN TRANSLATION
\* Label s1 of procedure s_semwait at line 29 col 9 changed to s1_
\* Label s2 of procedure s_semwait at line 30 col 11 changed to s2_
\* Label p0 of procedure s_sempost at line 39 col 9 changed to p0_
\* Label p1 of procedure s_sempost at line 42 col 9 changed to p1_
\* Label w1 of procedure x_semwait at line 48 col 9 changed to w1_
\* Label w2 of procedure x_semwait at line 49 col 11 changed to w2_
\* Label p1 of procedure x_sempost at line 61 col 9 changed to p1_x
VARIABLES total, lock, s_count, x_count, waiters, iterations, pc, stack

vars == << total, lock, s_count, x_count, waiters, iterations, pc, stack >>

ProcSet == ({"thr1", "thr2"})

Init == (* Global variables *)
        /\ total = 0
        /\ lock = 0
        /\ s_count = 0
        /\ x_count = 1
        /\ waiters = 0
        /\ iterations = [i \in  {"thr1", "thr2"} |-> N]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

l0(self) == /\ pc[self] = "l0"
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations, 
                            stack >>

l1(self) == /\ pc[self] = "l1"
            /\ IF lock = 0
                  THEN /\ lock' = 1
                       /\ pc' = [pc EXCEPT ![self] = "l_end"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l0"]
                       /\ lock' = lock
            /\ UNCHANGED << total, s_count, x_count, waiters, iterations, 
                            stack >>

l_end(self) == /\ pc[self] = "l_end"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                               iterations >>

mutex_lock(self) == l0(self) \/ l1(self) \/ l_end(self)

u0(self) == /\ pc[self] = "u0"
            /\ Assert(lock = 1, "Failure of assertion at line 21, column 9.")
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "u_end"]
            /\ UNCHANGED << total, s_count, x_count, waiters, iterations, 
                            stack >>

u_end(self) == /\ pc[self] = "u_end"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                               iterations >>

mutex_unlock(self) == u0(self) \/ u_end(self)

s0(self) == /\ pc[self] = "s0"
            /\ s_count' = s_count - 1
            /\ pc' = [pc EXCEPT ![self] = "s1_"]
            /\ UNCHANGED << total, lock, x_count, waiters, iterations, stack >>

s1_(self) == /\ pc[self] = "s1_"
             /\ pc' = [pc EXCEPT ![self] = "s2_"]
             /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                             iterations, stack >>

s2_(self) == /\ pc[self] = "s2_"
             /\ IF s_count > 0
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s1_"]
                        /\ stack' = stack
             /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                             iterations >>

s_iswaiting(self) == /\ pc[self] = "s_iswaiting"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "s1_"]
                     /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                                     iterations, stack >>

s_semwait(self) == s0(self) \/ s1_(self) \/ s2_(self) \/ s_iswaiting(self)

p0_(self) == /\ pc[self] = "p0_"
             /\ IF s_count < 1
                   THEN /\ s_count' = s_count + 1
                   ELSE /\ TRUE
                        /\ UNCHANGED s_count
             /\ pc' = [pc EXCEPT ![self] = "p1_"]
             /\ UNCHANGED << total, lock, x_count, waiters, iterations, stack >>

p1_(self) == /\ pc[self] = "p1_"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                             iterations >>

s_sempost(self) == p0_(self) \/ p1_(self)

w0(self) == /\ pc[self] = "w0"
            /\ x_count' = x_count - 1
            /\ pc' = [pc EXCEPT ![self] = "w1_"]
            /\ UNCHANGED << total, lock, s_count, waiters, iterations, stack >>

w1_(self) == /\ pc[self] = "w1_"
             /\ pc' = [pc EXCEPT ![self] = "w2_"]
             /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                             iterations, stack >>

w2_(self) == /\ pc[self] = "w2_"
             /\ IF x_count > 0
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "w1_"]
                        /\ stack' = stack
             /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                             iterations >>

w_iswaiting(self) == /\ pc[self] = "w_iswaiting"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "w1_"]
                     /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                                     iterations, stack >>

x_semwait(self) == w0(self) \/ w1_(self) \/ w2_(self) \/ w_iswaiting(self)

p0(self) == /\ pc[self] = "p0"
            /\ IF x_count < 1
                  THEN /\ x_count' = x_count + 1
                  ELSE /\ TRUE
                       /\ UNCHANGED x_count
            /\ pc' = [pc EXCEPT ![self] = "p1_x"]
            /\ UNCHANGED << total, lock, s_count, waiters, iterations, stack >>

p1_x(self) == /\ pc[self] = "p1_x"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                              iterations >>

x_sempost(self) == p0(self) \/ p1_x(self)

w1(self) == /\ pc[self] = "w1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "x_semwait",
                                                     pc        |->  "w2" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "w0"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

w2(self) == /\ pc[self] = "w2"
            /\ waiters' = waiters + 1
            /\ pc' = [pc EXCEPT ![self] = "w3"]
            /\ UNCHANGED << total, lock, s_count, x_count, iterations, stack >>

w3(self) == /\ pc[self] = "w3"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "x_sempost",
                                                     pc        |->  "w4" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

w4(self) == /\ pc[self] = "w4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_unlock",
                                                     pc        |->  "w5" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "u0"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

w5(self) == /\ pc[self] = "w5"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "s_semwait",
                                                     pc        |->  "w6" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "s0"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

w6(self) == /\ pc[self] = "w6"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_lock",
                                                     pc        |->  "Error" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

wait(self) == w1(self) \/ w2(self) \/ w3(self) \/ w4(self) \/ w5(self)
                 \/ w6(self)

s1(self) == /\ pc[self] = "s1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "x_semwait",
                                                     pc        |->  "s2" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "w0"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

s2(self) == /\ pc[self] = "s2"
            /\ IF waiters > 0
                  THEN /\ waiters' = waiters - 1
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "s_sempost",
                                                                pc        |->  "s4" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p0_"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s4"]
                       /\ UNCHANGED << waiters, stack >>
            /\ UNCHANGED << total, lock, s_count, x_count, iterations >>

s4(self) == /\ pc[self] = "s4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "x_sempost",
                                                     pc        |->  "Error" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

signal(self) == s1(self) \/ s2(self) \/ s4(self)

start(self) == /\ pc[self] = "start"
               /\ IF iterations[self] > 0
                     THEN /\ pc' = [pc EXCEPT ![self] = "p1"]
                     ELSE /\ Assert(iterations[self] = 0, 
                                    "Failure of assertion at line 92, column 5.")
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << total, lock, s_count, x_count, waiters, 
                               iterations, stack >>

p1(self) == /\ pc[self] = "p1"
            /\ IF s_count = 0 \/ x_count = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations, 
                            stack >>

p2(self) == /\ pc[self] = "p2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "signal",
                                                     pc        |->  "p3" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

p3(self) == /\ pc[self] = "p3"
            /\ IF s_count = 1 \/ s_count = 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "p4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations, 
                            stack >>

p4(self) == /\ pc[self] = "p4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                     pc        |->  "start" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << total, lock, s_count, x_count, waiters, iterations >>

temp(self) == start(self) \/ p1(self) \/ p2(self) \/ p3(self) \/ p4(self)

Next == (\E self \in ProcSet:  \/ mutex_lock(self) \/ mutex_unlock(self)
                               \/ s_semwait(self) \/ s_sempost(self)
                               \/ x_semwait(self) \/ x_sempost(self)
                               \/ wait(self) \/ signal(self))
           \/ (\E self \in {"thr1", "thr2"}: temp(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


======================================================
