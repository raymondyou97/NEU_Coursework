;;; While/Fork interpreter.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Main entry point.
;;;
;;; Given: abstract syntax tree for the program
;;; and a list of inputs to the program.
;;;
;;; Finds all of the variables mentioned by the program,
;;; noting which of them are inputs.
;;; Initializes all variables to their initial values,
;;; and then interprets the statements of the program.

(define (interpret pgm inputs)
  (call-with-values
   (lambda () (find-variables pgm))
   (lambda (input-variables other-variables)
     (if (not (= (length inputs)
                 (length input-variables)))
         (begin (display "wrong number of inputs:\n")
                (display "expected ")
                (display (length input-variables))
                (display " but got ")
                (display (length inputs))
                (newline)
                (exit 1)))
     (let* ((all-variables (append input-variables other-variables))
            (vars (list->vector all-variables))
            (vals (list->vector
                   (append inputs
                           (map (lambda (var) 0) other-variables)))))
       (let loop ((pgm pgm))
         (if (eq? (kind pgm) 'input)
             (loop (input.pgm pgm))
             (interp (list pgm) vars vals ticks/timeslice '())))))))

;;; Given the abstract syntax tree for a program, returns two lists:
;;;     the input variables (in order)
;;;     other variables (in unspecified order)

(define (find-variables pgm)

  ;; find the input variables

  (define (f ast in)
    (case (kind ast)
     ((input)
      (let ((x (var.name (input.var ast))))
        (if (memq x in)
            (begin (display "input variables must be distinct\n")
                   (exit 1)))
        (f (input.pgm ast) (cons x in))))
     (else
      (let* ((in (reverse in))
             (other (g ast in '())))
        (values in other)))))

  ;; find the other variables

  (define (g ast in other)
    (define (h ast other)
      (case (kind ast)
       ((output)
        (h (output.exp ast) other))
       ((accept reject skip)
        other)
       ((assign)
        (h (assign.rhs ast)
           (add-if-new (var.name (assign.lhs ast)) in other)))
       ((if)
        (h (if.test ast)
           (h (if.then ast)
              (h (if.else ast) other))))
       ((while)
        (h (while.test ast)
           (h (while.body ast) other)))
       ((sequence)
        (let loop ((stms (sequence.stms ast))
                   (other other))
          (if (null? stms)
              other
              (loop (rest stms)
                    (h (first stms) other)))))
       ((fork)
        (h (fork.exp1 ast)
           (h (fork.exp2 ast)
              (add-if-new (var.name (fork.var ast)) in other))))
       ((+ - * / < = >)
        (h (exp.left ast)
           (h (exp.right ast) other)))
       ((not)
        (h (not.exp ast) other))
       ((num)
        other)
       ((var)
        (add-if-new (var.name ast) in other))
       (else
        (display "bug in While/Fork interpreter:\n")
        (pretty-print ast))))
    (h ast other))

  (define (add-if-new x in other)
    (cond ((memq x in)
           other)
          ((memq x other)
           other)
          (else
           (cons x other))))

  (f pgm '()))

;;; Interpreter for lists of statements.
;;;
;;; Given:
;;;     a non-empty list of statements
;;;     a vector of variables
;;;     a vector of their values
;;;     value of a countdown timer
;;;     list of forked processes
;;;
;;; Might not return.  If it returns, it returns one of
;;;     #true  (meaning accept)
;;;     #false (meaning reject)
;;;
;;; Side effect:
;;;     If the program accepted by executing an output statement,
;;;     the value to be output is stored into the global variable
;;;     output-value.

(define (interp stms vars vals ticks processes)
  (let ((stm (first stms))
        (stms (rest stms))
        (ticks (- ticks 1)))
    (if (<= ticks 0)
        (if (null? processes)
            (interp (cons stm stms) vars vals ticks/timeslice processes)
            (let* ((this-process (makeProcess stms vals))
                   (that-process (first processes))
                   (processes (append (rest processes) (list this-process)))
                   (stms (process.stms that-process))
                   (vals (process.vals that-process)))
              (interp stms vars vals ticks/timeslice processes)))
        (case (kind stm)
         ((output)
          (let ((result (evaluate (output.exp stm) vars vals)))
            (set! output-value result)
            #t))
         ((accept)
          #t)
         ((reject)
          (if (null? processes)
              #f
              (let ((process (first processes))
                    (processes (rest processes)))
                (interp (process.stms process)
                        vars
                        (process.vals process)
                        ticks/timeslice
                        processes))))
         ((skip)
          (interp stms vars vals ticks processes))
         ((assign)
          (update! (var.name (assign.lhs stm))
                   (evaluate (assign.rhs stm) vars vals)
                   vars
                   vals)
          (interp stms vars vals ticks processes))
         ((if)
          (if (bevaluate (if.test stm) vars vals)
              (interp (cons (if.then stm) stms) vars vals ticks processes)
              (interp (cons (if.else stm) stms) vars vals ticks processes)))
         ((while)
          (if (bevaluate (while.test stm) vars vals)
              (interp (cons (while.body stm)
                            (cons stm stms))
                      vars vals ticks processes)
              (interp stms vars vals ticks processes)))
         ((sequence)
          (interp (append (sequence.stms stm) stms) vars vals ticks processes))
         ((fork)
          (interp-fork stm stms vars vals processes))
         (else
          (display "bug in While/Fork interpreter:\n")
          (pretty-print stm))))))

;;; Interpreter for fork statements.

(define (interp-fork stm stms vars vals processes)
  (let* ((n1 (evaluate (fork.exp1 stm) vars vals))
         (n2 (evaluate (fork.exp2 stm) vars vals))
         (n2-n1 (- n2 n1))
         (fork-ids (if (<= n1 n2)
                       (map (lambda (n) (+ n n1))
                            (iota (+ 1 n2-n1)))
                       '()))
         (x (var.name (fork.var stm)))
         (new-processes (map (lambda (id)
                           (let ((vals (vector-copy vals)))
                             (update! x id vars vals)
                             (makeProcess stms vals)))
                         fork-ids))
         (processes (append processes new-processes)))
    (if (null? processes)
        #f
        (let ((this-process (first processes))
              (processes (rest processes)))
          (interp (process.stms this-process)
                  vars
                  (process.vals this-process)
                  ticks/timeslice
                  processes)))))

;;; Interpreter for arithmetic expressions.

(define (evaluate exp vars vals)
  (case (kind exp)
   ((+ - * / < = >)
    (let ((n1 (evaluate (exp.left exp) vars vals))
          (n2 (evaluate (exp.right exp) vars vals)))
      (case (kind exp)
       ((+) (+ n1 n2))
       ((-) (- n1 n2))
       ((*) (* n1 n2))
       ((/) (if (zero? n2) 0 (div n1 n2))))))
   ((num)
    (num.val exp))
   ((var)
    (lookup (var.name exp) vars vals))
   (else
    (display "bug in While/Fork interpreter:\n")
    (pretty-print exp))))

;;; Interpreter for boolean expressions.

(define (bevaluate exp vars vals)
  (case (kind exp)
   ((< = >)
    (let ((n1 (evaluate (exp.left exp) vars vals))
          (n2 (evaluate (exp.right exp) vars vals)))
      (case (kind exp)
       ((<) (< n1 n2))
       ((=) (= n1 n2))
       ((>) (> n1 n2)))))
   ((not)
    (not (bevaluate (not.exp exp) vars vals)))
   (else
    (display "bug in While/Fork interpreter:\n")
    (pretty-print exp))))

;;; Returns the current value of x.

(define (lookup x vars vals)
  (let loop ((i 0))
    (if (eq? x (vector-ref vars i))
        (vector-ref vals i)
        (loop (+ i 1)))))

;;; Sets x to n.

(define (update! x n vars vals)
  (let loop ((i 0))
    (if (eq? x (vector-ref vars i))
        (vector-set! vals i n)
        (loop (+ i 1)))))
