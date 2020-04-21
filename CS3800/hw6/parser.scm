(define (parse-P)
  (case (next-token)
    ((fork begin
           while
           if
           id
           skip
           reject
           accept
           output)
     (let ((ast1 (parse-R)))
       (if (eq? (next-token) 'eof)
           (begin (consume-token!) (mkSequence ast1))
           (parse-error 'P '(eof)))))
    ((input)
     (begin
       (consume-token!)
       (let ((ast1 (parse-I)))
         (if (eq? (next-token) 'semicolon)
             (begin
               (consume-token!)
               (let ((ast2 (parse-P))) (mkInput ast1 ast2)))
             (parse-error 'P '(semicolon))))))
    (else
     (parse-error
       'P
       '(accept
          begin
          fork
          id
          if
          input
          output
          reject
          skip
          while)))))

(define (parse-R)
  (case (next-token)
    ((output)
     (begin
       (consume-token!)
       (let ((ast1 (parse-E))) (mkOutput ast1))))
    ((accept reject skip id if while begin fork)
     (let ((ast1 (parse-S)))
       (if (eq? (next-token) 'semicolon)
           (begin
             (consume-token!)
             (let ((ast2 (parse-R))) (cons ast1 ast2)))
           (parse-error 'R '(semicolon)))))
    (else
     (parse-error
       'R
       '(accept
          begin
          fork
          id
          if
          output
          reject
          skip
          while)))))

(define (parse-Q)
  (case (next-token)
    ((accept reject skip id if while begin fork)
     (let ((ast1 (parse-S)))
       (let ((ast2 (parse-Q2))) (cons ast1 ast2))))
    (else
     (parse-error
       'Q
       '(accept begin fork id if reject skip while)))))

(define (parse-Q2)
  (case (next-token)
    ((semicolon)
     (begin
       (consume-token!)
       (let ((ast1 (parse-Q))) (identity ast1))))
    ((end) (empty))
    (else (parse-error 'Q2 '(end semicolon)))))

(define (parse-S)
  (case (next-token)
    ((fork)
     (begin
       (consume-token!)
       (let ((ast1 (parse-I)))
         (if (eq? (next-token) 'assign)
             (begin
               (consume-token!)
               (let ((ast2 (parse-E)))
                 (if (eq? (next-token) 'through)
                     (begin
                       (consume-token!)
                       (let ((ast3 (parse-E))) (mkFork ast1 ast2 ast3)))
                     (parse-error 'S '(through)))))
             (parse-error 'S '(assign))))))
    ((begin)
     (begin
       (consume-token!)
       (let ((ast1 (parse-Q)))
         (if (eq? (next-token) 'end)
             (begin (consume-token!) (mkSequence ast1))
             (parse-error 'S '(end))))))
    ((while)
     (begin
       (consume-token!)
       (let ((ast1 (parse-B)))
         (if (eq? (next-token) 'do)
             (begin
               (consume-token!)
               (let ((ast2 (parse-S))) (mkWhile ast1 ast2)))
             (parse-error 'S '(do))))))
    ((if)
     (begin
       (consume-token!)
       (let ((ast1 (parse-B)))
         (if (eq? (next-token) 'then)
             (begin
               (consume-token!)
               (let ((ast2 (parse-S)))
                 (if (eq? (next-token) 'else)
                     (begin
                       (consume-token!)
                       (let ((ast3 (parse-S))) (mkIf ast1 ast2 ast3)))
                     (parse-error 'S '(else)))))
             (parse-error 'S '(then))))))
    ((id)
     (let ((ast1 (parse-I)))
       (if (eq? (next-token) 'assign)
           (begin
             (consume-token!)
             (let ((ast2 (parse-E))) (mkAssign ast1 ast2)))
           (parse-error 'S '(assign)))))
    ((skip) (begin (consume-token!) (mkSkip)))
    ((reject) (begin (consume-token!) (mkReject)))
    ((accept) (begin (consume-token!) (mkAccept)))
    (else
     (parse-error
       'S
       '(accept begin fork id if reject skip while)))))

(define (parse-E)
  (case (next-token)
    ((intliteral lparen id)
     (let ((ast1 (parse-T)))
       (let ((ast2 (parse-E2))) (mkExp ast1 ast2))))
    (else (parse-error 'E '(id intliteral lparen)))))

(define (parse-E2)
  (case (next-token)
    ((minus)
     (begin
       (consume-token!)
       (let ((ast1 (parse-T)))
         (let ((ast2 (parse-E2)))
           (mkPartialSub ast1 ast2)))))
    ((plus)
     (begin
       (consume-token!)
       (let ((ast1 (parse-T)))
         (let ((ast2 (parse-E2)))
           (mkPartialAdd ast1 ast2)))))
    ((then do
           gt
           equal
           lt
           rparen
           semicolon
           end
           else
           through
           eof)
     (mkNone))
    (else
     (parse-error
       'E2
       '(do else
            end
          eof
          equal
          gt
          lt
          minus
          plus
          rparen
          semicolon
          then
          through)))))

(define (parse-T)
  (case (next-token)
    ((id lparen intliteral)
     (let ((ast1 (parse-F)))
       (let ((ast2 (parse-T2))) (mkTerm ast1 ast2))))
    (else (parse-error 'T '(id intliteral lparen)))))

(define (parse-T2)
  (case (next-token)
    ((slash)
     (begin
       (consume-token!)
       (let ((ast1 (parse-F)))
         (let ((ast2 (parse-T2)))
           (mkPartialDiv ast1 ast2)))))
    ((asterisk)
     (begin
       (consume-token!)
       (let ((ast1 (parse-F)))
         (let ((ast2 (parse-T2)))
           (mkPartialMul ast1 ast2)))))
    ((minus plus
            eof
            through
            else
            end
            semicolon
            rparen
            lt
            equal
            gt
            do
            then)
     (mkNone))
    (else
     (parse-error
       'T2
       '(asterisk
          do
          else
          end
          eof
          equal
          gt
          lt
          minus
          plus
          rparen
          semicolon
          slash
          then
          through)))))

(define (parse-F)
  (case (next-token)
    ((intliteral)
     (let ((ast1 (parse-N))) (identity ast1)))
    ((lparen)
     (begin
       (consume-token!)
       (let ((ast1 (parse-E)))
         (if (eq? (next-token) 'rparen)
             (begin (consume-token!) (identity ast1))
             (parse-error 'F '(rparen))))))
    ((id) (let ((ast1 (parse-I))) (identity ast1)))
    (else (parse-error 'F '(id intliteral lparen)))))

(define (parse-B)
  (case (next-token)
    ((id lparen intliteral)
     (let ((ast1 (parse-E)))
       (let ((ast2 (parse-B2))) (mkBoolExp ast1 ast2))))
    ((not)
     (begin
       (consume-token!)
       (let ((ast1 (parse-B))) (mkNot ast1))))
    (else
     (parse-error 'B '(id intliteral lparen not)))))

(define (parse-B2)
  (case (next-token)
    ((gt)
     (begin
       (consume-token!)
       (let ((ast1 (parse-E))) (mkPartialGT ast1))))
    ((equal)
     (begin
       (consume-token!)
       (let ((ast1 (parse-E))) (mkPartialEQ ast1))))
    ((lt)
     (begin
       (consume-token!)
       (let ((ast1 (parse-E))) (mkPartialLT ast1))))
    (else (parse-error 'B2 '(equal gt lt)))))

(define (parse-I)
  (case (next-token)
    ((id) (begin (consume-token!) (mkVar)))
    (else (parse-error 'I '(id)))))

(define (parse-N)
  (case (next-token)
    ((intliteral) (begin (consume-token!) (mkNum)))
    (else (parse-error 'N '(intliteral)))))

