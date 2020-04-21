(define (scanner0)
  (define (state0 c)
    (case c
      ((#\<) (consumeChar) (accept 'lt))
      ((#\>) (consumeChar) (accept 'gt))
      ((#\=) (consumeChar) (accept 'equal))
      ((#\;) (consumeChar) (accept 'semicolon))
      ((#\-) (consumeChar) (accept 'minus))
      ((#\+) (consumeChar) (accept 'plus))
      ((#\*) (consumeChar) (accept 'asterisk))
      ((#\)) (consumeChar) (accept 'rparen))
      ((#\() (consumeChar) (accept 'lparen))
      ((#\newline #\vtab #\page #\return #\space)
       (consumeChar)
       (begin
         (set! string_accumulator_length 0)
         (state0 (scanChar))))
      ((#\/) (consumeChar) (state5 (scanChar)))
      ((#\:) (consumeChar) (state3 (scanChar)))
      ((#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
       (consumeChar)
       (state2 (scanChar)))
      ((#\a
        #\b
        #\c
        #\d
        #\e
        #\f
        #\g
        #\h
        #\i
        #\j
        #\k
        #\l
        #\m
        #\n
        #\o
        #\p
        #\q
        #\r
        #\s
        #\t
        #\u
        #\v
        #\w
        #\x
        #\y
        #\z)
       (consumeChar)
       (state1 (scanChar)))
      (else
       (if (eof-object? c)
           (begin (consumeChar) (accept 'eof))
           (scannerError errIncompleteToken)))))
  (define (state1 c)
    (case c
      ((#\a
        #\b
        #\c
        #\d
        #\e
        #\f
        #\g
        #\h
        #\i
        #\j
        #\k
        #\l
        #\m
        #\n
        #\o
        #\p
        #\q
        #\r
        #\s
        #\t
        #\u
        #\v
        #\w
        #\x
        #\y
        #\z)
       (consumeChar)
       (state1 (scanChar)))
      (else (accept 'id))))
  (define (state2 c)
    (case c
      ((#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
       (consumeChar)
       (state2 (scanChar)))
      (else (accept 'intliteral))))
  (define (state3 c)
    (case c
      ((#\=) (consumeChar) (accept 'assign))
      (else (scannerError errIncompleteToken))))
  (define (state4 c)
    (case c
      (else
       (if ((lambda (c)
              (and (char? c)
                   (not (char=? c (integer->char 10)))
                   (not (char=? c (integer->char 13)))))
            c)
           (begin (consumeChar) (state4 (scanChar)))
           (begin
             (set! string_accumulator_length 0)
             (state0 (scanChar)))))))
  (define (state5 c)
    (case c
      ((#\/) (consumeChar) (state4 (scanChar)))
      (else (accept 'slash))))
  (define (state6 c)
    (case c
      (else
       (begin
         (set! string_accumulator_length 0)
         (state0 (scanChar))))))
  (define (state7 c) (case c (else (accept 'eof))))
  (define (state8 c)
    (case c (else (accept 'lparen))))
  (define (state9 c)
    (case c (else (accept 'rparen))))
  (define (state10 c)
    (case c (else (accept 'asterisk))))
  (define (state11 c)
    (case c (else (accept 'plus))))
  (define (state12 c)
    (case c (else (accept 'minus))))
  (define (state13 c)
    (case c (else (accept 'semicolon))))
  (define (state14 c)
    (case c (else (accept 'assign))))
  (define (state15 c)
    (case c (else (accept 'equal))))
  (define (state16 c) (case c (else (accept 'gt))))
  (define (state17 c) (case c (else (accept 'lt))))
  (let loop ((c (scanChar)))
    (if (char-whitespace? c)
        (begin
          (consumeChar)
          (set! string_accumulator_length 0)
          (loop (scanChar)))))
  (let ((c (scanChar)))
    (if (char=? c EOF) (accept 'eof) (state0 c))))
