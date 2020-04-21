;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Lexical analyzer for While/FOrk
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Constants and local variables.

;;; Constants.

;;; Character that represents end of file.

(define EOF (integer->char 4))

;;; initial length of string_accumulator

(define initial_accumulator_length 64)

;;; Encodings of error messages.

(define errLongToken 1)                 ; extremely long token
(define errIncompleteToken 2)      ; any lexical error, really
(define errIllegalString 5)                   ; illegal string
(define errBug 12)           ; bug in reader, shouldn't happen
(define errLexGenBug 13)                        ; can't happen

;;; State for one-token buffering in lexical analyzer.

(define kindOfNextToken 'z1)      ; valid iff nextTokenIsReady
(define nextTokenIsReady #f)

(define tokenValue "")  ; string associated with current token

;;; A string buffer for the characters of the current token.
;;; Resized as necessary.

(define string_accumulator (make-string initial_accumulator_length))

;;; Number of characters in string_accumulator.

(define string_accumulator_length 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Lexical analyzer.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; next-token and consume-token! are called by the parser.

;;; Returns the current token.

(define (next-token)
  (if nextTokenIsReady
      kindOfNextToken
      (begin (set! string_accumulator_length 0)
             (scanner0))))

;;; Consumes the current token.

(define (consume-token!)
  (set! nextTokenIsReady #f))

;;; Called by the lexical analyzer's state machine.

(define (scannerError msg)

  (define msgtxt
    (cond ((= msg errLongToken)
           "amazingly long token")
          ((= msg errIncompleteToken)
           "incomplete or illegal token")
          ((= msg errIllegalString)
           "illegal string syntax")
          ((= msg errLexGenBug)
           "bug in lexical analyzer (generated)")
          (else "bug in lexical analyzer")))

  (let* ((c (scanChar))
         (next (if (char? c) (string c) ""))
         (line (+ 1 (port-lines-read input-port)))
         (msgtxt (string-append msgtxt
                                " in line "
                                (number->string line)))
         (irritant1 (substring string_accumulator
                               0
                               string_accumulator_length))
         (msgtxt (string-append msgtxt
                                ": "
                                irritant1
                                next)))

    ;; must avoid infinite loop on current input port

    (consumeChar)
    (display "lexical error: ")
    (display msgtxt)
    (newline)
    (write irritant1)
    (newline)
    (write next)
    (newline)
    (write input-port)
    (newline)
    (error "lexical error" msgtxt irritant1 next input-port))
  (next-token))

;;; Accepts a token of the given kind, returning that kind.
;;;
;;; For some kinds of tokens, a value for the token must also
;;; be recorded in tokenValue.

(define (accept t)
; (write (list t (substring string_accumulator 0 string_accumulator_length)))
; (newline)
  (case t

    ((intliteral)

     (set! tokenValue
           (substring string_accumulator
                      0 string_accumulator_length))
     (set! kindOfNextToken t)
     (set! nextTokenIsReady #t)
     t)

    ((id)

     (set! tokenValue
           (substring string_accumulator
                      0 string_accumulator_length))

     ;; Reserved words and typeids are recognized here.

     (let ((sym (string->symbol tokenValue)))
       (case sym
	 ((input output accept reject skip if then else while do
           begin end fork through not)
	  (set! kindOfNextToken sym))
	 (else
	  (set! kindOfNextToken t))))

     (set! nextTokenIsReady #t)
     kindOfNextToken)

    (else
     (set! kindOfNextToken t)
     (set! nextTokenIsReady #t)
     t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Character i/o, so to speak.
;;; Uses the input-port as input.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (scanChar)
  (let ((c (peek-char input-port)))
    (if (eof-object? c)
        EOF
        c)))

;;; Consumes the current character.  Returns unspecified values.

(define (consumeChar)
  (if (< string_accumulator_length (string-length string_accumulator))
      (let ((c (read-char input-port)))
        (if (char? c)
            (begin
              (string-set! string_accumulator
                           string_accumulator_length
                           c)
              (set! string_accumulator_length
                    (+ string_accumulator_length 1)))))
      (begin (expand-accumulator) (consumeChar))))

;;; Doubles the size of string_accumulator while
;;; preserving its contents.
;;;
;;; Insanely long tokens are not supported.

(define (expand-accumulator)
  (define maximum 4000000)
  (let* ((n (string-length string_accumulator))
         (newn (* 2 n))
         (newn (cond ((< newn maximum)
                      newn)
                     ((< n maximum)
                      maximum)
                     (else
                      (scannerError errLongToken))))
         (new (make-string newn)))
    (do ((i 0 (+ i 1)))
        ((= i n))
      (string-set! new i (string-ref string_accumulator i)))
    (set! string_accumulator new)))

;;; eof
