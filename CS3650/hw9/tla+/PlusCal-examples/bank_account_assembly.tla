---------------------------- MODULE bank_account_assembly ----------------------------
\* Copyright (c) 2017, Gene Cooperman.  May be freely distributed
\* and modified as long as this copyright notice remains.


\* Joint bank account by husband and wife; Only assembly statements (not C)
\*   are assumed atomic.  This version models the code at assembly level,
\*   and so the "if" statement is no longer atomic.  It will assert an error
\*   when total /= 120, even though initially, account = 100, and
\*                          cash["husband"] = cash["wife"] = 10.
\*   In the "Model" sub-window, try initializing the constant "N" to 1.
\*
\* Note that if you remove the labels
\*     w0b, w0c, w1b, d0b, d0c, d1b, then there will be no assertion error.

EXTENDS Naturals, Sequences, TLC  \* Sequences required for "procedure" stmt
CONSTANT N \* N is number of iterations.  Assign to it in model overview.

(*
--algorithm bank {
  variables account = 100, cash = [i \in {"husband", "wife"} |-> 10],
            iterations = [i \in  {"husband", "wife"} |-> N];
    \* Note that we need to define iterations["husband"] and iterations["wife"].
    \*   We do _not_ want a single global variable, iterations, that is
    \*   shared between "husband" and "wife".
    \* In model, replace "N" (a constant) by value for iterations

  \* The procedures withdraw and deposit have been translated here
  \*   to pseudo-assembly language
  \* Note that "register1" and "register2" were declared as local variables
  \*   inside the processes for husband and wife.
  procedure withdraw(amount1)
    variable register1, register2;
  {
    withdraw_start: register1 := amount1;         \* lw register1, (amount1)
     w0b:               register2 := account - register1;
              \* lw register2, (account) ; sub register2, register2, register1
     w0c:               account := register2;     \* sw register2, (account)
                    
     w1:            register2 := cash[self] + register1;
              \* lw register2, (cash[self]) ; add register2, register2, register1
     w1b:               cash[self] := register2;  \* sw register2, (cash[self])
                    
     w2:            return;
  }

  procedure deposit(amount1)
    variable register1, register2;
  {
   deposit_start: register1 := amount1;             \* lw register1, (amount1)
     d0b:         register2 := account + register1; \* lw register2, (account)
                                          \* add register2, register2, register1
     d0c:         account := register2;             \* sw register2, (account)
                    
     d1:          register2 := cash[self] - register1;
                                          \* lw register2, (cash[self])
                                          \* sub register2, register2, register1
     d1b:         cash[self] := register2;          \* sw register2, (cash[self])
                    
     d2:          return;
  }
  
  process (spouse \in {"husband", "wife"})
    variable total;
  { start: while (iterations[self] > 0) {
      \* We hard-wire the max amount below, but this could have been a CONSTANT.
      s1: with (amount \in 1..2)
            call withdraw(amount);
      s2: with (amount \in 1..2)
            call deposit(amount);
      s3: iterations[self] := iterations[self] - 1;
          total := account + cash["husband"] + cash["wife"];
      };
      assert iterations[self] = 0;
      
      if (iterations["husband"] = 0 /\ iterations["wife"] = 0) {
        total := account + cash["husband"] + cash["wife"];
        print total;
        assert total = 120 ;
      }
  } \* end process block

} \* end algorithm
*)
\* BEGIN TRANSLATION
\* Procedure variable register1 of procedure withdraw at line 33 col 14 changed to register1_
\* Procedure variable register2 of procedure withdraw at line 33 col 25 changed to register2_
\* Parameter amount1 of procedure withdraw at line 32 col 22 changed to amount1_
CONSTANT defaultInitValue
VARIABLES account, cash, iterations, pc, stack, amount1_, register1_, 
          register2_, amount1, register1, register2, total

vars == << account, cash, iterations, pc, stack, amount1_, register1_, 
           register2_, amount1, register1, register2, total >>

ProcSet == ({"husband", "wife"})

Init == (* Global variables *)
        /\ account = 100
        /\ cash = [i \in {"husband", "wife"} |-> 10]
        /\ iterations = [i \in  {"husband", "wife"} |-> N]
        (* Procedure withdraw *)
        /\ amount1_ = [ self \in ProcSet |-> defaultInitValue]
        /\ register1_ = [ self \in ProcSet |-> defaultInitValue]
        /\ register2_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure deposit *)
        /\ amount1 = [ self \in ProcSet |-> defaultInitValue]
        /\ register1 = [ self \in ProcSet |-> defaultInitValue]
        /\ register2 = [ self \in ProcSet |-> defaultInitValue]
        (* Process spouse *)
        /\ total = [self \in {"husband", "wife"} |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

withdraw_start(self) == /\ pc[self] = "withdraw_start"
                        /\ register1_' = [register1_ EXCEPT ![self] = amount1_[self]]
                        /\ pc' = [pc EXCEPT ![self] = "w0b"]
                        /\ UNCHANGED << account, cash, iterations, stack, 
                                        amount1_, register2_, amount1, 
                                        register1, register2, total >>

w0b(self) == /\ pc[self] = "w0b"
             /\ register2_' = [register2_ EXCEPT ![self] = account - register1_[self]]
             /\ pc' = [pc EXCEPT ![self] = "w0c"]
             /\ UNCHANGED << account, cash, iterations, stack, amount1_, 
                             register1_, amount1, register1, register2, total >>

w0c(self) == /\ pc[self] = "w0c"
             /\ account' = register2_[self]
             /\ pc' = [pc EXCEPT ![self] = "w1"]
             /\ UNCHANGED << cash, iterations, stack, amount1_, register1_, 
                             register2_, amount1, register1, register2, total >>

w1(self) == /\ pc[self] = "w1"
            /\ register2_' = [register2_ EXCEPT ![self] = cash[self] + register1_[self]]
            /\ pc' = [pc EXCEPT ![self] = "w1b"]
            /\ UNCHANGED << account, cash, iterations, stack, amount1_, 
                            register1_, amount1, register1, register2, total >>

w1b(self) == /\ pc[self] = "w1b"
             /\ cash' = [cash EXCEPT ![self] = register2_[self]]
             /\ pc' = [pc EXCEPT ![self] = "w2"]
             /\ UNCHANGED << account, iterations, stack, amount1_, register1_, 
                             register2_, amount1, register1, register2, total >>

w2(self) == /\ pc[self] = "w2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ register1_' = [register1_ EXCEPT ![self] = Head(stack[self]).register1_]
            /\ register2_' = [register2_ EXCEPT ![self] = Head(stack[self]).register2_]
            /\ amount1_' = [amount1_ EXCEPT ![self] = Head(stack[self]).amount1_]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << account, cash, iterations, amount1, register1, 
                            register2, total >>

withdraw(self) == withdraw_start(self) \/ w0b(self) \/ w0c(self)
                     \/ w1(self) \/ w1b(self) \/ w2(self)

deposit_start(self) == /\ pc[self] = "deposit_start"
                       /\ register1' = [register1 EXCEPT ![self] = amount1[self]]
                       /\ pc' = [pc EXCEPT ![self] = "d0b"]
                       /\ UNCHANGED << account, cash, iterations, stack, 
                                       amount1_, register1_, register2_, 
                                       amount1, register2, total >>

d0b(self) == /\ pc[self] = "d0b"
             /\ register2' = [register2 EXCEPT ![self] = account + register1[self]]
             /\ pc' = [pc EXCEPT ![self] = "d0c"]
             /\ UNCHANGED << account, cash, iterations, stack, amount1_, 
                             register1_, register2_, amount1, register1, total >>

d0c(self) == /\ pc[self] = "d0c"
             /\ account' = register2[self]
             /\ pc' = [pc EXCEPT ![self] = "d1"]
             /\ UNCHANGED << cash, iterations, stack, amount1_, register1_, 
                             register2_, amount1, register1, register2, total >>

d1(self) == /\ pc[self] = "d1"
            /\ register2' = [register2 EXCEPT ![self] = cash[self] - register1[self]]
            /\ pc' = [pc EXCEPT ![self] = "d1b"]
            /\ UNCHANGED << account, cash, iterations, stack, amount1_, 
                            register1_, register2_, amount1, register1, total >>

d1b(self) == /\ pc[self] = "d1b"
             /\ cash' = [cash EXCEPT ![self] = register2[self]]
             /\ pc' = [pc EXCEPT ![self] = "d2"]
             /\ UNCHANGED << account, iterations, stack, amount1_, register1_, 
                             register2_, amount1, register1, register2, total >>

d2(self) == /\ pc[self] = "d2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ register1' = [register1 EXCEPT ![self] = Head(stack[self]).register1]
            /\ register2' = [register2 EXCEPT ![self] = Head(stack[self]).register2]
            /\ amount1' = [amount1 EXCEPT ![self] = Head(stack[self]).amount1]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << account, cash, iterations, amount1_, register1_, 
                            register2_, total >>

deposit(self) == deposit_start(self) \/ d0b(self) \/ d0c(self) \/ d1(self)
                    \/ d1b(self) \/ d2(self)

start(self) == /\ pc[self] = "start"
               /\ IF iterations[self] > 0
                     THEN /\ pc' = [pc EXCEPT ![self] = "s1"]
                          /\ total' = total
                     ELSE /\ Assert(iterations[self] = 0, 
                                    "Failure of assertion at line 74, column 7.")
                          /\ IF iterations["husband"] = 0 /\ iterations["wife"] = 0
                                THEN /\ total' = [total EXCEPT ![self] = account + cash["husband"] + cash["wife"]]
                                     /\ PrintT(total'[self])
                                     /\ Assert(total'[self] = 120, 
                                               "Failure of assertion at line 79, column 9.")
                                ELSE /\ TRUE
                                     /\ total' = total
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << account, cash, iterations, stack, amount1_, 
                               register1_, register2_, amount1, register1, 
                               register2 >>

s1(self) == /\ pc[self] = "s1"
            /\ \E amount \in 1..2:
                 /\ /\ amount1_' = [amount1_ EXCEPT ![self] = amount]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "withdraw",
                                                             pc        |->  "s2",
                                                             register1_ |->  register1_[self],
                                                             register2_ |->  register2_[self],
                                                             amount1_  |->  amount1_[self] ] >>
                                                         \o stack[self]]
                 /\ register1_' = [register1_ EXCEPT ![self] = defaultInitValue]
                 /\ register2_' = [register2_ EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "withdraw_start"]
            /\ UNCHANGED << account, cash, iterations, amount1, register1, 
                            register2, total >>

s2(self) == /\ pc[self] = "s2"
            /\ \E amount \in 1..2:
                 /\ /\ amount1' = [amount1 EXCEPT ![self] = amount]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "deposit",
                                                             pc        |->  "s3",
                                                             register1 |->  register1[self],
                                                             register2 |->  register2[self],
                                                             amount1   |->  amount1[self] ] >>
                                                         \o stack[self]]
                 /\ register1' = [register1 EXCEPT ![self] = defaultInitValue]
                 /\ register2' = [register2 EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "deposit_start"]
            /\ UNCHANGED << account, cash, iterations, amount1_, register1_, 
                            register2_, total >>

s3(self) == /\ pc[self] = "s3"
            /\ iterations' = [iterations EXCEPT ![self] = iterations[self] - 1]
            /\ total' = [total EXCEPT ![self] = account + cash["husband"] + cash["wife"]]
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << account, cash, stack, amount1_, register1_, 
                            register2_, amount1, register1, register2 >>

spouse(self) == start(self) \/ s1(self) \/ s2(self) \/ s3(self)

Next == (\E self \in ProcSet: withdraw(self) \/ deposit(self))
           \/ (\E self \in {"husband", "wife"}: spouse(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====================
