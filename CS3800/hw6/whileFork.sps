(import (scheme base)
        (scheme char)
        (scheme cxr)
        (scheme read)
        (scheme write)
        (scheme file)
        (scheme process-context)
        (only (scheme list) every iota)
        (only (rnrs base) div assert)
        (primitives pretty-print port-lines-read))

(include "dfa.scm")
(include "lexer.scm")
(include "ast.scm")
(include "parser.scm")
(include "actions.scm")
(include "interp.scm")

(define (first x) (car x))
(define (rest x)  (cdr x))

;;; Representation of processes.

(define (makeProcess stms vals)
  (list stms vals))

(define (process.stms process)
  (car process))

(define (process.vals process)
  (cadr process))

(define ticks/timeslice 25)

;;; Command-line arguments.

(define cmds (command-line))

;(write cmds)
;(newline)

(if (not (<= 2 (length cmds)))
    (begin (display "no While/Fork program specified\n")
           (exit 1)))

(define args (cddr cmds))

(set! args (map string->number args))

(if (not (every number? args))
    (begin (display "non-numeric input was specified\n")
           (exit 1)))

(define input-file (cadr cmds))

(define input-port (open-input-file input-file))

(define pgm (parse-P))

;(pretty-print pgm)

(define output-value #f)

(define output (interpret pgm args))

(if output
    (display "\nAccepted\n")
    (display "\nRejected\n"))

(if (and output output-value)
    (begin (display "Output: ") (write output-value) (newline)))
