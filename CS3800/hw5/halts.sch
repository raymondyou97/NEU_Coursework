; Given the Goedel number of a Turing machine and
; a natural number to use as input to the machine,
; returns #t if the machine halts on that input.

(define (halts? m n)
  (call-with-values
   (lambda ()
     (run-turing-machine (machine m)
                         (vector->list
                          (make-vector n 1))))
   (lambda results #t)))

; The correspondence between natural numbers and
; Turing machines is implemented here.
;
; First let's define exactly what we mean by a
; Turing machine.  (The following definition is
; moderately compatible with Sipser's definition
; in his undergraduate textbook on the theory of
; computation, and is completely compatible with
; the Turing machine interpreter Clinger wrote
; for CS U390 during the spring 2007 semester.)
; 
; Turing machines always have exactly 1 halt state
; (which is represented by the Scheme symbol accept).
;
; The Turing machine alphabet is always {0,1}
; (which are represented by the Scheme symbol _,
; pronounced "blank", and the Scheme number 1).
;
; Turing machine tapes are half-infinite to the right.
; At the beginning of execution, the input is in
; unary notation (a sequence of 1s) at the beginning
; of the tape, followed by an infinite sequence of
; 0s (aka blanks).
;
; Except for the halt state, which has no transitions,
; every state has 2 transitions (depending on what it
; sees under the read head).  If the machine has N
; states (including the halt state), there are
; 2 x 2 x N possibilities for each of those transitions.
; That means there are 16 N^2 possibilities for each
; non-halt state, so there are (16 N^2)^(N-1) machines
; with N states.  For example:
;
;     N       number of different machines with N states
;     1                          1
;     2                         64
;     3                      20736
;     4                   16777216
;     5                25600000000
;     6             63403380965376
;
; We'll let 0 stand for the unique machine with 1 state,
; 1 through 64 stand for the 64 machines with 2 states,
; 65 through 20800 stand for the 20736 machines with 3 states,
; and so on.
;
; Algorithm for converting i into a Turing machine:
;     compute N
;     compute an index j into the machines with N states
;     let b be the low-order 4*(N-1) bits of j
;     let a be the high-order bits of j
;     interpret a as an encoding of the next-state function
;     interpret b as an encoding of the symbol/direction

; Given a natural number n,
; returns the number of Turing machines that have n states.

(define (distinct-machines n)
  (if (zero? n)
      0
      (expt (* 16 n n) (- n 1))))

; Given i, returns four values:
;   the number of states in Turing machine i
;   the index j into the machines with that many states
;   an encoding a of the next-state function
;   an encoding b of the symbol/direction function

(define (states&index&a&b i)
  (do ((n 1 (+ n 1))
       (k 0 (+ k (distinct-machines n))))
      ((> k i)
       (let* ((n (- n 1))
              (how-many (distinct-machines n))
              (j (- i (- k how-many)))
              (n-1 (- n 1))
              (b (if (zero? n-1) 0 (remainder j (* 16 n-1))))
              (a (if (zero? n-1) j (quotient j (* 16 n-1)))))
         (values n j a b)))))

; Given a natural number i,
; returns the description of Turing machine i
; in the representation expected by Clinger's
; Turing machine interpreter.

(define (machine i)
  (call-with-values
   (lambda () (states&index&a&b i))
   (lambda (n j a b)

     ; We don't need j,
     ; but it helps to know how much of a and b
     ; will be consumed by each non-halt state.

     (define a/state (* n n))
     (define b/state 16)

     ; Given:
     ;   k (the number of states we've processed so far)
     ;   transitions (the transitions for the first k states)
     ;   a (the unconsumed part of encoding a)
     ;   b (the unconsumed part of encoding b)
     ; Returns: Turing machine i

     (define (mach k transitions a b)
       (if (= k (- n 1))
           (reverse transitions)
           (mach (+ k 1)
                 (cons (make-transitions k
                                         (remainder a a/state)
                                         (remainder b b/state))
                       transitions)
                 (quotient a a/state)
                 (quotient b b/state))))

     ; Returns the two transitions for state k

     (define (make-transitions k a b)
       (let ((qk (make-state k))
             (qk1 (make-state (quotient a n)))
             (qk2 (make-state (remainder a n)))
             (new1 (if (even? b) '_ 1))
             (new2 (if (even? (quotient b 2)) '_ 1))
             (dir1 (if (even? (quotient b 4)) 'L 'R))
             (dir2 (if (even? (quotient b 8)) 'L 'R)))
         `(,qk (_ ,new1 ,dir1 ,qk1)
               (1 ,new2 ,dir2 ,qk2))))

     (define (make-state k)
       (if (= k (- n 1))
           'accept
           (string->symbol (string-append "q" (number->string k)))))

     (mach 0 '() a b))))
