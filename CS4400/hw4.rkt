#lang pl 04

#| BNF for the ALGAE language:
     <ALGAE> ::= <num>
               | True
               | False
               | { not <ALGAE> }
               | { and <ALGAE> <ALGAE> }
               | { or <ALAGE> <ALGAE> }
               | { + <ALGAE> ... }
               | { * <ALGAE> ... }
               | { - <ALGAE> <ALGAE> ... }
               | { / <ALGAE> <ALGAE> ... }
               | { with { <id> <ALGAE> } <ALGAE> }
               | { if <ALGAE> <ALGAE> <ALGAE> }
               | <id>
               | { < <ALGAE> <ALGAE> }
               | { = <ALGAE> <ALGAE> }
               | { <= <ALGAE> <ALGAE> }
|#

;; ALGAE abstract syntax trees
(define-type ALGAE
  [Num  Number]
  [Bool Boolean]
  [Add  (Listof ALGAE)]
  [Mul  (Listof ALGAE)]
  [Sub  ALGAE (Listof ALGAE)]
  [Div  ALGAE (Listof ALGAE)]
  [Id   Symbol]
  [With Symbol ALGAE ALGAE]
  [If ALGAE ALGAE ALGAE]
  [Less ALGAE ALGAE]
  [Equal ALGAE ALGAE]
  [LessEq ALGAE ALGAE])

(: Not : ALGAE -> ALGAE)
;; Fake binding for not
(define (Not expr)
  (If expr (Bool #f) (Bool #t)))

(: And : ALGAE ALGAE -> ALGAE)
;; Fake binding for and
(define (And expr1 expr2)
  (If expr1 (If expr2 (Bool #t) (Bool #f)) (Bool #f)))

(: Or : ALGAE ALGAE -> ALGAE)
;; Fake binding for or
(define (Or expr1 expr2)
  (If expr1 (Bool #t) (If expr2 (Bool #t) (Bool #f))))

(: parse-sexpr : Sexpr -> ALGAE)
;; parses s-expressions into ALGAEs
(define (parse-sexpr sexpr)
  ;; utility for parsing a list of expressions
  (: parse-sexprs : (Listof Sexpr) -> (Listof ALGAE))
  (define (parse-sexprs sexprs) (map parse-sexpr sexprs))
  (match sexpr
    [(number: n) (Num n)]
    [(symbol: name)
     (match name
       ['True (Bool true)]
       ['False (Bool false)]
       [else (Id name)])]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(list 'if cnd then else) (If (parse-sexpr cnd)
                                  (parse-sexpr then)
                                  (parse-sexpr else))]
    [(list '+ args ...) (Add (parse-sexprs args))]
    [(list '* args ...) (Mul (parse-sexprs args))]
    [(list '- fst args ...) (Sub (parse-sexpr fst) (parse-sexprs args))]
    [(list '/ fst args ...) (Div (parse-sexpr fst) (parse-sexprs args))]
    [(list '< fst scnd) (Less (parse-sexpr fst) (parse-sexpr scnd))]
    [(list '= fst scnd) (Equal (parse-sexpr fst) (parse-sexpr scnd))]
    [(list '<= fst scnd) (LessEq (parse-sexpr fst) (parse-sexpr scnd))]
    [(list 'not arg) (Not (parse-sexpr arg))]
    [(list 'and arg1 arg2) (And (parse-sexpr arg1) (parse-sexpr arg2))]
    [(list 'or arg1 arg2) (Or (parse-sexpr arg1) (parse-sexpr arg2))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> ALGAE)
;; parses a string containing an ALGAE expression to an ALGAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

#| Formal specs for `subst':
   (`N' is a <num>, `E1', `E2' are <ALGAE>s, `x' is some <id>, `y' is a
   *different* <id>, `B' is a True/False)
      N[v/x]                = N
      B[v/x]                = B
      {+ E ...}[v/x]        = {+ E[v/x] ...}
      {* E ...}[v/x]        = {* E[v/x] ...}
      {- E1 E ...}[v/x]     = {- E1[v/x] E[v/x] ...}
      {/ E1 E ...}[v/x]     = {/ E1[v/x] E[v/x] ...}
      {< E1 E2 }[v/x]       = {< E1[v/x] E2[v/x]}
      {= E1 E2 }[v/x]       = {= E1[v/x] E2[v/x]}
      {<= E1 E2 }[v/x]       = {<= E1[v/x] E2[v/x]}
      y[v/x]                = y
      x[v/x]                = v
      {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
      {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
|#

(: subst : ALGAE Symbol ALGAE -> ALGAE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  ;; convenient helper -- no need to specify `from' and `to'
  (: subst* : ALGAE -> ALGAE)
  (define (subst* x) (subst x from to))
  ;; helper to substitute lists
  (: substs* : (Listof ALGAE) -> (Listof ALGAE))
  (define (substs* exprs) (map subst* exprs))
  (cases expr
    [(Num n) expr]
    [(Bool b) expr]
    [(Add args) (Add (substs* args))]
    [(Mul args) (Mul (substs* args))]
    [(Sub fst args) (Sub (subst* fst) (substs* args))]
    [(Div fst args) (Div (subst* fst) (substs* args))]
    [(Less fst scnd) (Less (subst* fst) (subst* scnd))]
    [(Equal fst scnd) (Equal (subst* fst) (subst* scnd))]
    [(LessEq fst scnd) (LessEq (subst* fst) (subst* scnd))]
    [(Id name) (if (eq? name from) to expr)]
    [(With bound-id named-expr bound-body)
     (With bound-id
           (subst* named-expr)
           (if (eq? bound-id from)
             bound-body
             (subst* bound-body)))]
    [(If cnd then else) (If (subst* cnd) (subst* then) (subst* else))]))

#| Formal specs for `eval':
     eval(N)            = N
     eval(B)            = B
     eval({+ E ...})    = evalN(E) + ...
     eval({* E ...})    = evalN(E) * ...
     eval({- E})        = -evalN(E)
     eval({/ E})        = 1/evalN(E)
     eval({- E1 E ...}) = evalN(E1) - (evalN(E) + ...)
     eval({/ E1 E ...}) = evalN(E1) / (evalN(E) * ...)
     eval(id)           = error!
     eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
     eval({< E1 E2})    = evalN(E1) < evalN(E2)
     eval({= E1 E2})    = evalN(E1) = evalN(E2)
     eval({<= E1 E2})    = evalN(E1) <= evalN(E2)
     eval({not E})      = eval({if E False True})
     eval({or E1 E2})   = eval({if E1 True {if E2 True False}})
     eval({and E1 E2})  = eval({if E1 {if E2 True False} False})
     evalN(E)           = eval(E) if it is a number, error otherwise
|#

(: eval-number : ALGAE -> Number)
;; helper for `eval': verifies that the result is a number
(define (eval-number expr)
  (let ([result (eval expr)])
    (if (number? result)
      result
      (error 'eval-number "need a number when evaluating ~s, but got ~s"
             expr result))))

(: eval-boolean : ALGAE -> Boolean)
;; helper for `eval': verifies that the result is a boolean
(define (eval-boolean expr)
  (let ([result (eval expr)])
    (if (boolean? result)
      result
      (error 'eval-boolean "need a boolean when evaluating ~s, but got ~s"
             expr result))))

(: value->algae : (U Number Boolean) -> ALGAE)
;; converts a value to an ALGAE value (so it can be used with `subst')
(define (value->algae val)
  (cond [(number? val) (Num val)]
        [(boolean? val) (Bool val)]
        ;; Note: a `cond' doesn't make much sense now, but it will when
        ;; we extend the language with booleans.  Also, since we use
        ;; Typed Racket, the type checker makes sure that this function
        ;; is never called with something that is not in its type, so
        ;; there's no need for an `else' branch like
        ;;     [else (error 'value->algae "unexpected value: ~s" val)]
        ;; (Strictly speaking, there's no need for the last predicate
        ;; (which is the only one here until you extend this), but it's
        ;; left in for clarity.)
        ))

(: eval : ALGAE -> (U Number Boolean))
;; evaluates ALGAE expressions by reducing them to numbers
(define (eval expr)
  (cases expr
    [(Num n) n]
    [(Bool b) b]
    [(Add args) (foldl + 0 (map eval-number args))]
    [(Mul args) (foldl * 1 (map eval-number args))]
    [(Sub fst args) (if (null? args)
                        (- 0 (eval-number fst))
                        (- (eval-number fst)
                           (foldl + 0 (map eval-number args))))]
    [(Div fst args)(let ([result (foldl * 1 (map eval-number args))])
                     (if (zero? result)
                         (error 'eval "division by zero")
                         (/ (eval-number fst) result)))]
    [(Less fst scnd) (< (eval-number fst) (eval-number scnd))]
    [(Equal fst scnd) (equal? (eval-number fst) (eval-number scnd))]
    [(LessEq fst scnd) (<= (eval-number fst) (eval-number scnd))]
    [(With bound-id named-expr bound-body)
     (eval (subst bound-body
                  bound-id
                  ;; see the above `value->algae' helper
                  (value->algae (eval named-expr))))]
    [(If cnd then else) (if (eval-boolean cnd) (eval then) (eval else))]
    [(Id name) (error 'eval "free identifier: ~s" name)]))

(: run : String -> (U Boolean Number))
;; evaluate an ALGAE program contained in a string
(define (run str)
  (eval (parse str)))

;; tests (for simple expressions)
(test (run "5") => 5)
(test (run "{}") =error> "parse-sexpr: bad syntax in ()")
(test (run "{+}") => 0)
(test (run "{+ 1}") => 1)
(test (run "{+ 1 1}") => 2)
(test (run "{+ 1 1 1}") => 3)
(test (run "{-}") =error> "parse-sexpr: bad syntax in (-)")
(test (run "{- 1}") => -1)
(test (run "{- 1 1}") => 0)
(test (run "{- 1 1 1}") => -1) 
(test (run "{*}") => 1)
(test (run "{* 5}") => 5)
(test (run "{* 5 5}") => 25)
(test (run "{* 5 5 5}") => 125)
(test (run "{/}") =error> "parse-sexpr: bad syntax in (/)")
(test (run "{/ 1 0}") =error> "eval: division by zero")
(test (run "{/ 1}") => 1)
(test (run "{/ 1 1}") => 1)
(test (run "{/ 1 1 1}") => 1)
(test (run "{/ 0 1}") => 0)
(test (run "{/ 25 5 5}") => 1)
(test (run "{with {x {+ 5 5}} {+ x x}}") => 20)
(test (run "{with {x {* 2 2}} {* x x}}") => 16)
(test (run "{with {x {* 2 2}} {/ 16 x}}") => 4)
(test (run "{with {x 5} {+ x x}}") => 10)
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") => 14)
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") => 4)
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") => 15)
(test (run "{with {x 5} {+ x {with {x 3} x}}}") => 8)
(test (run "{with {x 5} {+ x {with {y 3} x}}}") => 10)
(test (run "{with {x 5} {with {y x} y}}") => 5)
(test (run "{with {x 5} {with {x x} x}}") => 5)
(test (run "{with {x} {+ x x }}") =error>
      "parse-sexpr: bad `with' syntax in (with (x) (+ x x))")
(test (run "{+ 5 5 {}}") =error> "parse-sexpr: bad syntax in ()")
(test (run "{+ 5 x}") =error> "eval: free identifier: x")
(test (run "True"))
(test (not (run "False")))
(test (run "{< 1 3}"))
(test (not (run "{< 3 1}")))
(test (run "{= 3 3}"))
(test (run "{<= 3 6}"))
(test (run "{<= 3 3}"))
(test (not (run "{<= 3 1}")))
(test (run "{if True 1 2}") => 1)
(test (run "{if False 1 2}") => 2)
(test (run "{if {< 1 3} 1 2}") => 1)
(test (run "{if {< 3 1} 1 2}") => 2)
(test (run "{if {<= 1 1} 1 2}") => 1)
(test (run "{if {<= 1 2} 1 2}") => 1)
(test (run "{if {<= 2 1} 1 2}") => 2)
(test (run "{if {= 1 1} 1 2}") => 1)
(test (run "{if {= 1 2} 1 2}") => 2)
(test (run "{if 1 1 2}")
      =error> (string-append "eval-boolean: need a boolean when evaluating "
                             "#(struct:Num 1), but got 1"))
(test (run "{with {x True} {if x x False}}"))
(test (not (run "{with {x False} {if x x False}}")))
(test (not (run "{with {x {<= 4 3}} {if x x False}}")))
(test (run "{+ True}")
      =error> (string-append "eval-number: need a number when evaluating "
                             "#(struct:Bool #t), but got #t"))
(test (not (run "{with {x 5} {< x 3}}")))
(test (run "{with {x 5} {= x 5}}"))
(test (run "{with {x 5} {<= x 5}}"))
(test (not (run "{not True}")))
(test (run "{or True False}"))
(test (not (run "{or False False}")))
(test (run "{and True True}"))
(test (not (run "{and True False}")))
(test (run "{and {< 1 3} {< 1 2}}"))
(test (run "{or {= 1 3} {< 1 2}}"))
(test (not (run "{or {= 1 3} {< 3 2}}")))
(test (not (run "{not {and {< 1 3} {< 1 2}}}")))
(test (run "{not {and {= 1 3} {< 1 2}}}"))
(test (not (run "{and {not True} {not True}}")))
(test (not (run "{and {not True} {not False}}")))
(test (run "{and {not False} {not False}}"))
(test (not (run "{or {not True} {not True}}")))
(test (run "{or {not True} {not False}}"))
(test (run "{or {not False} {not True}}"))

(define minutes-spent 360)
