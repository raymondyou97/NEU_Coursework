; Copyright 2007 William D Clinger.
;
; Permission to copy this software, in whole or in part, to use this
; software for any lawful purpose, and to redistribute this software
; is granted subject to the restriction that all copies made of this
; software must include this copyright notice in full.
;
; I also request that you send me a copy of any improvements that you
; make to this software so that they may be incorporated within it to
; the benefit of the Scheme community.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Turing Machine simulator, written in portable R5RS Scheme.
;
; Simulates unidirectional single-tape Turing Machines
; as formalized in Michael Sipser's textbook,
; Introduction to the Theory of Computation, Second Edition,
; Thompson Course Technology, 2006.
; 
; Usage:
;
;     (run tm input)
;     (run tm input output-port)
;     (run tm input output-file)
;     (run-turing-machine tm input)
;     (run-turing-machine tm input output-port)
;     (run-turing-machine tm input output-file)
;
; where tm is the description of a Turing machine,
; input is a list of symbols and numbers
; that is taken to be the initial contents of the tape,
; output-port (if specified) is an output port,
; output-file (if specified) is a string naming an output file.
;
; A trace will be written to the output-port or output-file,
; or to the current output port is no output-port or output-file
; is specified.
;
; If the Turing machine halts on the input,
; then two values will be returned:
;     a boolean (#t means accept, #f means reject)
;     the tape contents when the machine halted
; 
; The description of the Turing machine to be simulated
; follows http://web.mit.edu/manoli/turing/www/turing.html
;
;     ((state (old new direction next) ...) ...)
;
; where state and next are states,
; old and new are tape symbols,
; and direction is the symbol L or R.
; 
; The tape symbol * acts as a wildcard that matches any tape symbol.
; The * wildcard may be used as the old symbol,
; and may be used as the new symbol for transitions that use it
; as the old symbol (in which case it means the tape will be left
; unchanged).
; 
; The accept and reject states are common to every Turing machine,
; but they are both halting states so they have no transitions
; and should not be listed in the description of the machine.
; 
; The input is represented as a list of tape symbols,
; which should be Scheme symbols and/or numbers,
; with blanks implied to the right.
; A blank is represented by the symbol _, which should
; not appear in the input.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Number of steps to run before timing out.
; Setting this value to -1 disables the timeout feature.

(define maxsteps 100000)
;(define maxsteps 2000)

; Given the description of a Turing machine,
; an input,
; and an optional output file name or output port,
; the simulator returns two values (if it returns at all):
;     a boolean (#t means accept, #f means reject)
;     the tape contents when the machine halted
;
; If the optional output file or port is specified,
; then a trace of the Turing machine's execution
; is output to that file or port.  Otherwise the
; trace will be written to the current output port.
; The trace will be more readable if all tape symbols
; have the same length.

(define (run tm input . rest)
  (if (null? rest)
      (run-turing-machine tm input (current-output-port))
      (run-turing-machine tm input (car rest))))

; Given the description of a Turing machine,
; an input,
; and an optional output file name or output port,
; the simulator returns two values (if it returns at all):
;     a boolean (#t means accept, #f means reject)
;     the tape contents when the machine halted
;
; If the optional output file or port is specified,
; then a trace of the Turing machine's execution
; is output to that file or port.
; The trace will be more readable if all tape symbols
; have the same length.

(define (run-turing-machine tm input . rest)
  (if (null? rest)
      (simulate-turing-machine tm input #f maxsteps)
      (let ((x (car rest)))
        (cond ((string? x)
               ;(delete-file x)         ; would not be portable R5RS Scheme
               (call-with-output-file
                x
                (lambda (out) (simulate-turing-machine tm input out maxsteps))))
              ((output-port? x)
               (simulate-turing-machine tm input x maxsteps))
              (else
               (display "Invalid optional argument to run-turing-machine: ")
               (write x)
               (newline))))))

; Accessors for the components of a transition.

(define transition-old car)             ; when old is under the tape head
(define transition-new cadr)            ; new replaces old
(define transition-direction caddr)     ; the head moves L or R
(define transition-next cadddr)         ; and goes into the next state

(define (check boolean msg)
  (if boolean
      #t
      (begin (display "ERROR:\n")
             (display msg)
             (newline)
             #f)))

(define (check2 boolean msg transitions)
  (if boolean
      #t
      (begin (display "ERROR:\n")
             (display msg)
             (newline)
             (write transitions)
             (newline)
             #f)))

; Given a description of a Turing machine,
; an input, an output port (or #f),
; and some number of steps (or -1),
; simulates the Turing machine on the input
; while writing a trace to the output port.

(define (simulate-turing-machine tm input out steps)
  (if (and (check (list? tm) "description of TM is not a list")
           (check (list? input) "input is not a list")
           (or (eqv? out #f)
               (output-port? out))
           (check (for-all list? tm) "description of TM state is not a list")
           (check (for-all (lambda (x) (or (symbol? x) (number? x))) input)
                  "some input element is not in tape alphabet")
           (check (for-all positive? (map length tm))
                  "description of TM state is empty")
           (check (for-all symbol? (map car tm)) "illegal name for TM state")
           (let ((transition-lists (map cdr tm)))
             (and (for-all (lambda (transitions)
                             (check2
                              (and
                                  (for-all list? transitions)
                                  (for-all
                                   (lambda (transition)
                                     (and (= 4 (length transition))
                                          (let ((old (transition-old
                                                      transition))
                                                (new (transition-new
                                                      transition))
                                                (dir (transition-direction
                                                      transition))
                                                (next (transition-next
                                                       transition)))
                                            (and (or (symbol? old)
                                                     (number? old))
                                                 (or (symbol? new)
                                                     (number? new))
                                                 (or (eq? dir 'L)
                                                     (eq? dir 'R))
                                                 (symbol? next)))))
                                   transitions))
                              "illegal state transitions" transitions))
                           transition-lists))))
      (let ((start (if (null? tm) 'accept (caar tm))))
        (simulate tm (list->vector input) 0 start out steps))
      (begin (display "invalid argument to simulate-turing-machine: ")
             (newline)
             (display "    ") (write tm) (newline)
             (display "    ") (write input) (newline)
             (display "    ") (write out) (newline))))

; Given a description of a Turing machine,
; a vector representing the current tape,
; an index into that vector representing the current position,
; the current state,
; an output port (or #f),
; and some number of steps to take before giving up (or -1),
; simulates the Turing machine on the input
; while writing a trace to the output port.

(define (simulate tm tape head q out steps)
  (let ((tape (simplify-tape tm tape head q out)))
    (cond ((eq? q 'accept)
           (accept tape head out))
          ((eq? q 'reject)
           (reject tape head out))
          ((= steps 0)
           (timeout tape head out))
          (else
           (let ((state-transitions (assq q tm))
                 (steps (if (negative? steps) -1 (- steps 1))))
             (if state-transitions
                 (let* ((transitions (cdr state-transitions))
                        (transition (assv (vector-ref tape head) transitions)))
                   (if transition
                       (let ((new (transition-new transition))
                             (dir (transition-direction transition))
                             (next (transition-next transition)))
                         (vector-set! tape head new)
                         (simulate tm
                                   tape
                                   (if (eq? dir 'L)
                                       (max 0 (- head 1))
                                       (+ head 1))
                                   next
                                   out
                                   steps))
                       (let ((transition (assq '* transitions)))
                         (if transition
                             (let ((new (transition-new transition))
                                   (dir (transition-direction transition))
                                   (next (transition-next transition)))
                               (if (not (eq? '* new))
                                   (vector-set! tape head new))
                               (simulate tm
                                         tape
                                         (if (eq? dir 'L)
                                             (max 0 (- head 1))
                                             (+ head 1))
                                         next
                                         out
                                         steps))
                             (begin
                              (display "No transition for current state: ")
                              (write (list q (vector-ref tape head)))
                              (newline))))))
                 (begin (display "No transitions given for current state: ")
                        (write q) (newline))))))))

; Outputs appropriate message and returns appropriate values.

(define (accept tape head out)
  (if out
      (begin
       (display "Accepted" out)
       (newline out)))
  (values #t (vector->list tape)))

(define (reject tape head out)
  (if out
      (begin
       (display "Rejected" out)
       (newline out)))
  (values #f (vector->list tape)))

(define (timeout tape head out)
  (if out
      (begin
       (display "Timed Out" out)
       (newline out)))
  (values #f (vector->list tape)))

; Returns a possibly trimmed or extended vector of tape symbols.
; As a side effect, writes the current state to the output port.

(define (simplify-tape tm tape head q out)
  (let ((n (vector-length tape)))
    (cond ((>= head n)
           (simplify-tape tm
                          (list->vector (append (vector->list tape) '(_)))
                          head q out))
          ((and (< head (- n 1))
                (eq? '_ (vector-ref tape (- n 1))))
           (let ((tape (list->vector
                        (reverse
                         (cdr (reverse (vector->list tape)))))))
             (simplify-tape tm tape head q out)))
          (else
           (if out (display-state! tm tape head q out))
           tape))))

; Displays the current state.

(define (display-state! tm tape head q out)
  (do ((i 0 (+ i 1)))
      ((>= i head))
    (display " " out)
    (write (vector-ref tape i) out))
  (display "@" out)
  (write (vector-ref tape head) out)
  (do ((i (+ head 1)
       (+ i 1)))
      ((>= i (vector-length tape)))
    (display " " out)
    (write (vector-ref tape i) out))
  (display "    " out)
  (write q out)
  (newline out))

; Given a unary predicate
; and a list of values on which the predicate is defined,
; returns #t if the predicate is true of every value in the list
; and returns #f otherwise.

(define (for-all p? vals)
  (if (null? vals)
      #t
      (and (p? (car vals))
           (for-all p? (cdr vals)))))

; Test machine from
; http://web.mit.edu/manoli/turing/www/turing.html

(define (basic-tests)
  (define flip
    '(
      (s1 (1 1 L s1)
          (0 1 R s2))
      (s2 (1 0 R s2)
          (0 1 L s3))
      (s3 (0 0 L s3)
          (1 1 R s4))
      (s4 (0 0 L accept))))
  (run-turing-machine flip '(0 1 1 1 1 1 1 0) (current-output-port)))
#;
(basic-tests)
