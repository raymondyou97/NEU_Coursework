; Table of tokens and the symbolic names of their kinds.

(define character-classes
  '((isEOF eof-object?)
    (isAscii
     (lambda (c)
       (and (char? c)
            (char<=? c (integer->char 127)))))
    (isNotNewline
     (lambda (c)
       (and (char? c)
            (not (char=? c (integer->char 10)))      ; linefeed
            (not (char=? c (integer->char 13)))))))) ; return

; Expands symbols like %a..z into (! #\a #\b ... #\z).

(define (expand-ranges spec)
  (cond ((pair? spec)
         (cons (expand-ranges (car spec))
               (expand-ranges (cdr spec))))
        ((and (symbol? spec)
              (let ((s (symbol->string spec)))
                (and (= 5 (string-length s))
                     (char=? (string-ref s 0) #\%)
                     (char=? (string-ref s 2) #\.)
                     (char=? (string-ref s 3) #\.)
                     s)))
         =>
         (lambda (s)
           (let* ((c1 (string-ref s 1))
                  (c2 (string-ref s 4))
                  (n2 (char->integer c2)))
             (do ((i (char->integer c1) (+ i 1))
                  (chars '() (cons (integer->char i) chars)))
                 ((> i n2)
                  (cons '! (reverse chars)))))))
        (else spec)))

; Regular expressions for the lexical tokens of While/Fork.

(define whileForkTokens
  (expand-ranges
   '(

     ; The scanner generator treats whitespace specially,
     ; so the most common kinds of <interlexeme space>
     ; are called whitespace here.

     (whitespace (! #;#\tab #\linefeed #\vtab #\page #\return #\space
                    (#\/ #\/ (* isNotNewline))))

     ; An end of file generates a token.

     (eof isEOF)

     (lparen #\()
     (rparen #\))
     (asterisk #\*)
     (plus #\+)
     (minus #\-)
     (slash #\/)
     (semicolon #\;)
     (assign (#\: #\=))
     (equal #\=)
     (gt #\>)
     (lt #\<)

     (intliteral (%0..9 (* %0..9)))

     ;; reserved words are first recognized as identifiers

     (id (%a..z (* %a..z))))))

