(import (scheme base)
        (scheme cxr)
        (scheme file)
        (scheme process-context)
        (scheme read)
        (scheme write)
        )

(include "turing.scm")

(define reading-message
  "Reading from standard input...\n")

(define usage-message
  (string-append
   "Usage: turing <machine>\n\n"
   "    where <machine> is a file describing a Turing machine\n"
   "    and the input list will be read from standard input\n"))

(define file-not-found-message
  " not found\n")

(define args (cdr (command-line)))

(if (not (= 1 (length args)))
    (begin (display usage-message)
           (exit 1)))

(define machine-file (car args))

(if (not (file-exists? machine-file))
    (begin (display machine-file)
           (display file-not-found-message)
           (exit 1)))

(display reading-message)

(define machine
  (call-with-input-file
   machine-file
   read))

(define input (read))

(run machine input)

(exit)
