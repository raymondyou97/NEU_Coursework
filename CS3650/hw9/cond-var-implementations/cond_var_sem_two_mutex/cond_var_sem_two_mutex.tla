---------------------------- MODULE cond_var_sem_two_mutex ----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANT N
(*
--algorithm threads {
  variables total = 0, lock = 0, count = 0, m_waiters = 0, m_signals = 0,
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
    p0: count := count + 1;
    p1: return;
  }
  
  
  procedure wait() {
     w1: m_waiters := m_waiters + 1;
     w2: call mutex_unlock();
     w3: call sem_wait();
     w4: call mutex_lock();
     w5: m_waiters := m_waiters - 1;
     w6: m_signals := m_signals - 1;
  }
  
  procedure signal() {
     s1: call mutex_lock();
     s2: if(m_waiters > m_signals) {
            call sem_post();
     s3:    m_signals := m_signals + 1;
         };
     s4: call mutex_unlock();
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
\* Label p1 of procedure sem_post at line 40 col 9 changed to p1_
VARIABLES total, lock, count, m_waiters, m_signals, iterations, pc, stack

vars == << total, lock, count, m_waiters, m_signals, iterations, pc, stack >>

ProcSet == ({"thr1", "thr2"})

Init == (* Global variables *)
        /\ total = 0
        /\ lock = 0
        /\ count = 0
        /\ m_waiters = 0
        /\ m_signals = 0
        /\ iterations = [i \in  {"thr1", "thr2"} |-> N]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

l0(self) == /\ pc[self] = "l0"
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations, stack >>

l1(self) == /\ pc[self] = "l1"
            /\ IF lock = 0
                  THEN /\ lock' = 1
                       /\ pc' = [pc EXCEPT ![self] = "l_end"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l0"]
                       /\ lock' = lock
            /\ UNCHANGED << total, count, m_waiters, m_signals, iterations, 
                            stack >>

l_end(self) == /\ pc[self] = "l_end"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                               iterations >>

mutex_lock(self) == l0(self) \/ l1(self) \/ l_end(self)

u0(self) == /\ pc[self] = "u0"
            /\ Assert(lock = 1, "Failure of assertion at line 21, column 9.")
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "u_end"]
            /\ UNCHANGED << total, count, m_waiters, m_signals, iterations, 
                            stack >>

u_end(self) == /\ pc[self] = "u_end"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                               iterations >>

mutex_unlock(self) == u0(self) \/ u_end(self)

w0(self) == /\ pc[self] = "w0"
            /\ count' = count - 1
            /\ pc' = [pc EXCEPT ![self] = "w1_"]
            /\ UNCHANGED << total, lock, m_waiters, m_signals, iterations, 
                            stack >>

w1_(self) == /\ pc[self] = "w1_"
             /\ pc' = [pc EXCEPT ![self] = "w2_"]
             /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                             iterations, stack >>

w2_(self) == /\ pc[self] = "w2_"
             /\ IF count > 0
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "w1_"]
                        /\ stack' = stack
             /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                             iterations >>

w_iswaiting(self) == /\ pc[self] = "w_iswaiting"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "w1_"]
                     /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                                     iterations, stack >>

sem_wait(self) == w0(self) \/ w1_(self) \/ w2_(self) \/ w_iswaiting(self)

p0(self) == /\ pc[self] = "p0"
            /\ count' = count + 1
            /\ pc' = [pc EXCEPT ![self] = "p1_"]
            /\ UNCHANGED << total, lock, m_waiters, m_signals, iterations, 
                            stack >>

p1_(self) == /\ pc[self] = "p1_"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                             iterations >>

sem_post(self) == p0(self) \/ p1_(self)

w1(self) == /\ pc[self] = "w1"
            /\ m_waiters' = m_waiters + 1
            /\ pc' = [pc EXCEPT ![self] = "w2"]
            /\ UNCHANGED << total, lock, count, m_signals, iterations, stack >>

w2(self) == /\ pc[self] = "w2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_unlock",
                                                     pc        |->  "w3" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "u0"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

w3(self) == /\ pc[self] = "w3"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sem_wait",
                                                     pc        |->  "w4" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "w0"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

w4(self) == /\ pc[self] = "w4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_lock",
                                                     pc        |->  "w5" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

w5(self) == /\ pc[self] = "w5"
            /\ m_waiters' = m_waiters - 1
            /\ pc' = [pc EXCEPT ![self] = "w6"]
            /\ UNCHANGED << total, lock, count, m_signals, iterations, stack >>

w6(self) == /\ pc[self] = "w6"
            /\ m_signals' = m_signals - 1
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << total, lock, count, m_waiters, iterations, stack >>

wait(self) == w1(self) \/ w2(self) \/ w3(self) \/ w4(self) \/ w5(self)
                 \/ w6(self)

s1(self) == /\ pc[self] = "s1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_lock",
                                                     pc        |->  "s2" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

s2(self) == /\ pc[self] = "s2"
            /\ IF m_waiters > m_signals
                  THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sem_post",
                                                                pc        |->  "s3" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p0"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s4"]
                       /\ stack' = stack
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

s3(self) == /\ pc[self] = "s3"
            /\ m_signals' = m_signals + 1
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << total, lock, count, m_waiters, iterations, stack >>

s4(self) == /\ pc[self] = "s4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "mutex_unlock",
                                                     pc        |->  "Error" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "u0"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

signal(self) == s1(self) \/ s2(self) \/ s3(self) \/ s4(self)

start(self) == /\ pc[self] = "start"
               /\ IF iterations[self] > 0
                     THEN /\ pc' = [pc EXCEPT ![self] = "p1"]
                     ELSE /\ Assert(iterations[self] = 0, 
                                    "Failure of assertion at line 71, column 5.")
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                               iterations, stack >>

p1(self) == /\ pc[self] = "p1"
            /\ IF count = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations, stack >>

p2(self) == /\ pc[self] = "p2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "signal",
                                                     pc        |->  "p3" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

p3(self) == /\ pc[self] = "p3"
            /\ IF count = 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "p4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations, stack >>

p4(self) == /\ pc[self] = "p4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                     pc        |->  "start" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << total, lock, count, m_waiters, m_signals, 
                            iterations >>

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
