------------------------ MODULE lock_free_stack_ABA ------------------------

\*******************************************************************
\* Copyright (c) 2017, Gene Cooperman.  May be freely distributed
\* and modified as long as this copyright notice remains.
\*
\* For ABA problem, see:  https://en.wikipedia.org/wiki/ABA_problem
\*
\* NOTE:  The label "pop2a" in popStack() below "causes" the bug to be
\*        exposed.  Try deleting it. This would have the effect
\*        of atomically executing:
\*          CAS( HEAD, local_myhead, address[local_myhead].next );
\*        because it hides the internal assembly code that first
\*        computes the register value, reg_next, and then executes CAS().
\*
\*        Note that the field "onStack" is present only for debugging,
\*        and for assertions.  Don't hesitate to add extra fields and
\*        variables to ease the job of model checking.
\*
\*        The bug is the ABA problem.  When illustrating this bug,
\*        the errors in the "Model Checking Results" tab will have
\*        too many frames to easily read.  You can then remove many
\*        of the unnecessary labels in other routines to easily see
\*        the cause of the bug:  the ABA problem.
\*******************************************************************

EXTENDS Naturals, Sequences, TLC, FiniteSets

\* Parameters of the spec
CONSTANTS MAX_ITER, NUM_THREADS, MAX_STACK_SIZE

\* null is a unique value
NULL == CHOOSE n: n \notin 1..MAX_STACK_SIZE

(*
--algorithm LockFreeStack {
variables retVal = [thread \in 1..NUM_THREADS |-> NULL],
          address = [ addr \in 1..MAX_STACK_SIZE |->
                      [next |-> NULL, onStack |-> FALSE, data |-> 0] ],
          initialized = FALSE;
          HEAD ;

\* CAS:  compare-and-swap
\* CAS must be a macro.  Thisreflects that it is an assembly instruction
\*   that modifies its arguments. It must not use the call-by-value of a procedure.
\* CAS is atomic.  So, there are no intermediate labels.
macro CAS(x, y, z)
{
  if (x = y) {
    x := z; \* swap y for z as value of x
    retVal[self] := TRUE;
  } else {
    retVal[self] := FALSE;
  } ;
}

procedure pushStack(elt)
  variable local_myhead;
{
  push1: address[elt].next := HEAD;
  push2: assert address[elt].onStack = FALSE;
  push3: address[elt].onStack := TRUE;
  tryAgainPush: local_myhead := HEAD;
        push5a: address[elt].next := local_myhead;
        push5b: CAS( HEAD, local_myhead, elt );
        push5c: if (~retVal[self]) {
        push5d:   goto tryAgainPush;
                } ;
  endPush:  return;
}

procedure popStack()
  variable local_myhead, reg_next, elt;
{
  tryAgainPop:
     local_myhead := HEAD;
  pop1: if (local_myhead = 0) { \* If I believe HEAD = 0, return now.
  pop1a:  retVal[self] := NULL;
  pop1b:  return;
        } ;

  pop2:  reg_next :=  address[local_myhead].next;
  pop2a: CAS( HEAD, local_myhead, reg_next );
  pop2b: if (~retVal[self]) {
  pop2c:   goto tryAgainPop;
         } ;
  pop3: elt := local_myhead;
  pop4: assert address[elt].onStack = TRUE;
  pop5: address[elt].onStack := FALSE;              
  endPop: retVal[self] := elt ;
  return;
}

process (thread \in 1..NUM_THREADS)
  variable my_set = {}, myelt,
           init_thread, iterations = MAX_ITER ;
{
  init1: init_thread := CHOOSE thr \in 1..NUM_THREADS : TRUE ;
  init2: if (self = init_thread) { \* This thread will initialize global data
  init4:   HEAD := 0;
  init5:   while (HEAD < MAX_STACK_SIZE) {
  init6:     address[HEAD+1] := [ next |-> HEAD, onStack |-> TRUE, data |-> 1 ];
  init7:     HEAD := HEAD+1;
           } ;
  init8:   initialized := TRUE; \* init_thread will set this global var
         } ;
  init9: await initialized; \* all threads will wait for this

  th1: while (iterations > 0) {
  th2:   either {if (my_set /= {}) {
  th2a:           with (tmp \in my_set) { myelt := tmp } ; \* Set myelt at random (non-deterministically)
  th2b:           my_set := my_set \ {myelt};
  th2c:           call pushStack(myelt);
               } }
         or {
  th3a:      call popStack();
  th3b:      if (retVal[self] /= NULL) {
  th3c:        my_set := my_set \cup { retVal[self] } \* Add the popped elt to my_set
             } };
  th4: iterations := iterations - 1 ;
  } ; \* end while
} ; \* end process

} \* end algorithm

*)
=============================================================================
\* Modification History
\* Last modified Thu Nov 09 17:14:51 EST 2017 by gene
\* Last modified Sun Oct 22 06:26:25 EDT 2017 by celestekostopulos-cooperman
\* Created Fri Oct 20 22:08:53 EDT 2017 by celestekostopulos-cooperman
