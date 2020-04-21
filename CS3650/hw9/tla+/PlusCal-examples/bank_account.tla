---------------------------- MODULE bank_account ----------------------------
\* Copyright (c) 2017, Gene Cooperman.  May be freely distributed
\* and modified as long as this copyright notice remains.

\* Joint bank account by husband and wife; C statements are assumed atomic.

EXTENDS Naturals, Sequences, TLC  \* Sequences required for "procedure" stmt
CONSTANT N \* N is number of iterations.  Assign to it in model overview.

(*
--algorithm bank {
  variables account = 100, cash = [i \in {"husband", "wife"} |-> 10],
            iterations = [i \in  {"husband", "wife"} |-> N];
    \* Note that we need to define iterations["husband"] and iterations["wife"].
    \*   We do _not_ want a single global variable, iterations, that is
    \*   shared between "husband" and "wife".
    \* In model, replace defaultInitValue by value for iterations

  procedure withdraw(amount1) {
    withdraw_start: account := account - amount1;
     w1:            cash[self] := cash[self] + amount1;
     w2:            return;
  }

  procedure deposit(amount2) {
    deposit_start: account := account + amount2;
    d1:            cash[self] := cash[self] - amount2;
    d2:            return;
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
CONSTANT defaultInitValue
VARIABLES account, cash, iterations, pc, stack, amount1, amount2, total

vars == << account, cash, iterations, pc, stack, amount1, amount2, total >>

ProcSet == ({"husband", "wife"})

Init == (* Global variables *)
        /\ account = 100
        /\ cash = [i \in {"husband", "wife"} |-> 10]
        /\ iterations = [i \in  {"husband", "wife"} |-> N]
        (* Procedure withdraw *)
        /\ amount1 = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure deposit *)
        /\ amount2 = [ self \in ProcSet |-> defaultInitValue]
        (* Process spouse *)
        /\ total = [self \in {"husband", "wife"} |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

withdraw_start(self) == /\ pc[self] = "withdraw_start"
                        /\ account' = account - amount1[self]
                        /\ pc' = [pc EXCEPT ![self] = "w1"]
                        /\ UNCHANGED << cash, iterations, stack, amount1, 
                                        amount2, total >>

w1(self) == /\ pc[self] = "w1"
            /\ cash' = [cash EXCEPT ![self] = cash[self] + amount1[self]]
            /\ pc' = [pc EXCEPT ![self] = "w2"]
            /\ UNCHANGED << account, iterations, stack, amount1, amount2, 
                            total >>

w2(self) == /\ pc[self] = "w2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ amount1' = [amount1 EXCEPT ![self] = Head(stack[self]).amount1]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << account, cash, iterations, amount2, total >>

withdraw(self) == withdraw_start(self) \/ w1(self) \/ w2(self)

deposit_start(self) == /\ pc[self] = "deposit_start"
                       /\ account' = account + amount2[self]
                       /\ pc' = [pc EXCEPT ![self] = "d1"]
                       /\ UNCHANGED << cash, iterations, stack, amount1, 
                                       amount2, total >>

d1(self) == /\ pc[self] = "d1"
            /\ cash' = [cash EXCEPT ![self] = cash[self] - amount2[self]]
            /\ pc' = [pc EXCEPT ![self] = "d2"]
            /\ UNCHANGED << account, iterations, stack, amount1, amount2, 
                            total >>

d2(self) == /\ pc[self] = "d2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ amount2' = [amount2 EXCEPT ![self] = Head(stack[self]).amount2]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << account, cash, iterations, amount1, total >>

deposit(self) == deposit_start(self) \/ d1(self) \/ d2(self)

start(self) == /\ pc[self] = "start"
               /\ IF iterations[self] > 0
                     THEN /\ pc' = [pc EXCEPT ![self] = "s1"]
                          /\ total' = total
                     ELSE /\ Assert(iterations[self] = 0, 
                                    "Failure of assertion at line 42, column 7.")
                          /\ IF iterations["husband"] = 0 /\ iterations["wife"] = 0
                                THEN /\ total' = [total EXCEPT ![self] = account + cash["husband"] + cash["wife"]]
                                     /\ PrintT(total'[self])
                                     /\ Assert(total'[self] = 120, 
                                               "Failure of assertion at line 47, column 9.")
                                ELSE /\ TRUE
                                     /\ total' = total
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << account, cash, iterations, stack, amount1, 
                               amount2 >>

s1(self) == /\ pc[self] = "s1"
            /\ \E amount \in 1..2:
                 /\ /\ amount1' = [amount1 EXCEPT ![self] = amount]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "withdraw",
                                                             pc        |->  "s2",
                                                             amount1   |->  amount1[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "withdraw_start"]
            /\ UNCHANGED << account, cash, iterations, amount2, total >>

s2(self) == /\ pc[self] = "s2"
            /\ \E amount \in 1..2:
                 /\ /\ amount2' = [amount2 EXCEPT ![self] = amount]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "deposit",
                                                             pc        |->  "s3",
                                                             amount2   |->  amount2[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "deposit_start"]
            /\ UNCHANGED << account, cash, iterations, amount1, total >>

s3(self) == /\ pc[self] = "s3"
            /\ iterations' = [iterations EXCEPT ![self] = iterations[self] - 1]
            /\ total' = [total EXCEPT ![self] = account + cash["husband"] + cash["wife"]]
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << account, cash, stack, amount1, amount2 >>

spouse(self) == start(self) \/ s1(self) \/ s2(self) \/ s3(self)

Next == (\E self \in ProcSet: withdraw(self) \/ deposit(self))
           \/ (\E self \in {"husband", "wife"}: spouse(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====================
