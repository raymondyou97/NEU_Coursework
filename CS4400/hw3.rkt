#lang pl 03

;; ** The PUWAE interpreter


#| BNF for the PUWAE language:
     <PUWAE> ::= <num>
             | { + <PUWAE> <PUWAE> }
             | { - <PUWAE> <PUWAE> }
             | { * <PUWAE> <PUWAE> }
             | { / <PUWAE> <PUWAE> }
             | { with { <id> <PUWAE> } <PUWAE> }
             | <id>
             | { post <POST> ... }

     <POST> ::= <PUWAE>
            | +
            | -
            | *
            | /
|#

(define-type PostfixItem = (U PUWAE '+ '- '* '/))

;; PUWAE abstract syntax trees
(define-type PUWAE
  [Num  Number]
  [Add  PUWAE PUWAE]
  [Sub  PUWAE PUWAE]
  [Mul  PUWAE PUWAE]
  [Div  PUWAE PUWAE]
  [Id   Symbol]
  [With Symbol PUWAE PUWAE]
  [Post (Listof PostfixItem)])

(: parse-post-item : Sexpr -> PostfixItem)
;; parse an s-expression to a post-item
(define (parse-post-item x)
  (match x
    ['+ '+]
    ['- '-]
    ['* '*]
    ['/ '/]
    [else (parse-sexpr x)]))

(: parse-sexpr : Sexpr -> PUWAE)
;; parses s-expressions into PUWAEs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name) (Id name)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'post (sexpr: s) ...)(Post (map parse-post-item s))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> PUWAE)
;; parses a string containing a PUWAE expression to a PUWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

#| Formal specs for `subst':
   (`N' is a <num>, `E1', `E2' are <PUWAE>s, `x' is some <id>,
   `y' is a *different* <id>)
      N[v/x]                = N
      {+ E1 E2}[v/x]        = {+ E1[v/x] E2[v/x]}
      {- E1 E2}[v/x]        = {- E1[v/x] E2[v/x]}
      {* E1 E2}[v/x]        = {* E1[v/x] E2[v/x]}
      {/ E1 E2}[v/x]        = {/ E1[v/x] E2[v/x]}
      y[v/x]                = y
      x[v/x]                = v
      {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
      {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
|#

(: subst : PUWAE Symbol PUWAE -> PUWAE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (: post-subst : PostfixItem -> PostfixItem)
  (define (post-subst item)
    (if (symbol? item) item (subst item from to)))
  (cases expr
    [(Num n) expr]
    [(Add l r) (Add (subst l from to) (subst r from to))]
    [(Sub l r) (Sub (subst l from to) (subst r from to))]
    [(Mul l r) (Mul (subst l from to) (subst r from to))]
    [(Div l r) (Div (subst l from to) (subst r from to))]
    [(Post items) (Post (map post-subst items))]
    [(Id name) (if (eq? name from) to expr)]
    [(With bound-id named-expr bound-body)
     (With bound-id
           (subst named-expr from to)
           (if (eq? bound-id from)
             bound-body
             (subst bound-body from to)))]))

#| Formal specs for `eval':
     eval(N)         = N
     eval({+ E1 E2}) = eval(E1) + eval(E2)
     eval({- E1 E2}) = eval(E1) - eval(E2)
     eval({* E1 E2}) = eval(E1) * eval(E2)
     eval({/ E1 E2}) = eval(E1) / eval(E2)
     eval(id)        = error!
     eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
|#


(: post-eval : (Listof PostfixItem) (Listof Number) -> Number)
;; evaluates a postfix sequence of items, using a stack
(define (post-eval items stack)
  (if (null? items) 
    (match stack
      [(list (number: n)) n]
      [else (error `post-eval "invalid postfix sequence")])
    (let ([1st  (first items)]
          [more (rest items)])
      (: pop2-and-apply :
         (Number Number * -> Number)
         (Listof PostfixItem) (Listof Number) -> Number)
      (define (pop2-and-apply op items stack)
        (match stack
          [(list (number: n1) (number: n2))
           (post-eval items (list (op n2 n1)))]
          [else (error `pop2-and-apply
                       "two values needed for operation: ~s ~s" items stack)]))
      (cond [(eq? '+ 1st) (pop2-and-apply + more stack)]
            [(eq? '- 1st) (pop2-and-apply - more stack)]
            [(eq? '* 1st) (pop2-and-apply * more stack)]
            [(eq? '/ 1st) (pop2-and-apply / more stack)]
            [else (post-eval more (cons (eval 1st) stack))]))))


(: eval : PUWAE -> Number)
;; evaluates PUWAE expressions by reducing them to numbers
(define (eval expr)
  (cases expr
    [(Num n) n]
    [(Add l r) (+ (eval l) (eval r))]
    [(Sub l r) (- (eval l) (eval r))]
    [(Mul l r) (* (eval l) (eval r))]
    [(Div l r) (/ (eval l) (eval r))]
    [(With bound-id named-expr bound-body)
     (eval (subst bound-body
                  bound-id
                  (Num (eval named-expr))))]
    [(Id name) (error 'eval "free identifier: ~s" name)]
    [(Post items) (post-eval items '())]))

(: run : String -> Number)
;; evaluate a PUWAE program contained in a string
(define (run str)
  (eval (parse str)))

;; tests
(test (run "5") => 5)
(test (run "{+ 5 5}") => 10)
(test (run "{- 60 10}") => 50)
(test (run "{* 5 5}") => 25)
(test (run "{/ 5 5}") => 1)
(test (run "{with {x 5} {+ x x}}") => 10)
(test (run "{with {x 5} {- x x}}") => 0)
(test (run "{with {x 5} {* x x}}") => 25)
(test (run "{with {x 5} {/ x x}}") => 1)
(test (run "{with {x {+ 5 5}} {+ x x}}") => 20)
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") => 4)
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") => 14)
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") => 15)
(test (run "{with {x 5} {+ x {with {x 3} x}}}") => 8)
(test (run "{with {x 5} {+ x {with {y 3} x}}}") => 10)
(test (run "{with {x 5} {* x x}}") => 25)
(test (run "{with {x {* 5 5}} {/ x x}}") => 1)
(test (run "{with {x 5} {with {y x} y}}") => 5)
(test (run "{with {x 5} {with {x x} x}}") => 5)
(test (run "{with {x 1} y}") =error> "free identifier")
(test (run "{5 5}") =error> "parse-sexpr: bad syntax in (5 5)")
(test (run "{with {x} y}") =error>
      "parse-sexpr: bad `with' syntax in (with (x) y)")
(test (run "{post 3 1 +}") => 4)
(test (run "{post 3 1 -}") => 2)
(test (run "{post 3 1 *}") => 3)
(test (run "{post 6 2 /}") => 3)
(test (run "{* {post 1 2 +} {post 3 4 +}}") => 21)
(test (run "{post 1 2 + {+ 3 4} *}") => 21)
(test (run "{post {post 1 2 +} {post 3 4 +} *}") => 21)
(test (run "{* {+ {post 1} {post 2}} {+ {post 3} {post 4}}}") => 21)
(test (run "{with {x {post 3 4 +}} {post 1 2 + x *}}") => 21)
(test (run "{post}") =error> "invalid postfix sequence")
(test (run "{post }") =error> "invalid postfix sequence")
(test (run "{postt}") =error> "parse-sexpr: bad syntax in (postt)")
(test (run "{post 3 -}") =error>
      "pop2-and-apply: two values needed for operation: () (3)")
(test (run "{post 3 - -}") =error>
      "pop2-and-apply: two values needed for operation: (-) (3)")
(test (run "{post 3 4 - -}") =error>
      "pop2-and-apply: two values needed for operation: () (-1)")
(test (run "{post 3 4 5 -}") =error>
      "pop2-and-apply: two values needed for operation: () (5 4 3)")


(define minutes-spent 240)
