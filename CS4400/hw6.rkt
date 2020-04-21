#lang pl 06

;; ** The BRANG interpreter, using environments


#|
The grammar:
  <BRANG> ::= <num>
            | { + <BRANG> <BRANG> }
            | { - <BRANG> <BRANG> }
            | { * <BRANG> <BRANG> }
            | { / <BRANG> <BRANG> }
            | <id>
            | { with { <id> <BRANG> } <BRANG> }
            | { fun { (<id> <id> ...) } <BRANG> }
            | { call <BRANG> (<BRANG> <BRANG> ...) }

Evaluation rules:
  eval(N,env)                = N
  eval({+ E1 E2},env)        = eval(E1,env) + eval(E2,env)
  eval({- E1 E2},env)        = eval(E1,env) - eval(E2,env)
  eval({* E1 E2},env)        = eval(E1,env) * eval(E2,env)
  eval({/ E1 E2},env)        = eval(E1,env) / eval(E2,env)
  eval(CRef(x), env)         = list-ref(env,x)
  eval({fun {x} E},env)      = <{fun {x} E}, env>
  eval({call E1 E2},env1)
           = eval(Ef,extend(x,eval(E2,env1),env2))
                             if eval(E1,env1) = <{fun {x} Ef}, env2>
           = error!          otherwise
|#

(define-type BRANG
  [Num  Number]
  [Add  BRANG BRANG]
  [Sub  BRANG BRANG]
  [Mul  BRANG BRANG]
  [Div  BRANG BRANG]
  [Id   Symbol]
  [With Symbol BRANG BRANG]
  [Fun  (Listof Symbol) BRANG]
  [Call BRANG (Listof BRANG)])

(define-type CORE
  [CNum  Number]
  [CAdd  CORE CORE]
  [CSub  CORE CORE]
  [CMul  CORE CORE]
  [CDiv  CORE CORE]
  [CRef  Natural]
  [CFun  CORE]
  [CCall CORE CORE])

(: parse-sexpr : Sexpr -> BRANG)
;; parses s-expressions into BRANGs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name) (Id name)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(cons 'fun more)
     (match sexpr
       [(list 'fun (list (symbol: names) ...) body)
        (if (null? names)
            (error
             'parse-sexpr "bad `fun' syntax with 0 arguments in ~s" sexpr)
            (Fun names (parse-sexpr body)))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(cons 'call more)
     (match sexpr
       [(list 'call fun (sexpr: arg) (sexpr: args) ...)
        (Call (parse-sexpr fun) (map parse-sexpr (cons arg args)))]
       [else (error 'parse-sexpr
                    "bad `call' syntax with missing arguments in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: preprocess : BRANG DE-ENV -> CORE)
;; translates BRANG to CORE language, with deBrujin indices as the identifiers
(define (preprocess brang de-env)
  (cases brang
    [(Num n) (CNum n)]
    [(Add l r) (CAdd (preprocess l de-env) (preprocess r de-env))]
    [(Sub l r) (CSub (preprocess l de-env) (preprocess r de-env))]
    [(Mul l r) (CMul (preprocess l de-env) (preprocess r de-env))]
    [(Div l r) (CDiv (preprocess l de-env) (preprocess r de-env))]
    [(Id id) (CRef (de-env id))]
    [(With ids named-expr bound-body)
     (CCall (preprocess (Fun (list ids) bound-body) de-env)
            (preprocess named-expr de-env))]
    [(Fun ids bound-body)
     (let ([args (if (null? (rest ids))
                     bound-body
                     (Fun (rest ids) bound-body))])
     (CFun (preprocess args (de-extend de-env (first ids)))))]
    [(Call fun-expr arg-exprs)
     (let ([f-arg (first arg-exprs)]
           [r-args (rest arg-exprs)])
     ;; check if more than one arg passed in
     (if (> (length arg-exprs) 1)
         ;; translate to curried function, one arg at a game
       (preprocess (Call (Call fun-expr (list f-arg)) r-args) de-env)
       ;; return final core with preprocessed func and single arg
       (CCall (preprocess fun-expr de-env) (preprocess f-arg de-env))))]))

(: parse : String -> BRANG)
;; parses a string containing a BRANG expression to a BRANG AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; Types for environments, values, and a lookup function

(define-type ENV = (Listof VAL))

(define-type VAL
  [NumV Number]
  [FunV CORE ENV])

;; A 'compile-time env' from identifiers to de-Brujin indexes
(define-type DE-ENV = Symbol -> Natural)

(: de-empty-env : Symbol -> Natural)
;; the empty, error 'environment'
(define (de-empty-env id)
  (error 'de-empty-env "No mapping found for ~s" id))

(: de-extend : DE-ENV Symbol -> DE-ENV)
;; consumes a DE-ENV and a symbol and returns the extended environment
(define (de-extend de-env id)
  (lambda (id2)
    (if (equal? id id2)
        0
        (+ 1 (de-env id2)))))

(: NumV->number : VAL -> Number)
;; convert a BRANG runtime numeric value to a Racket one
(define (NumV->number val)
  (cases val
    [(NumV n) n]
    [else (error 'arith-op "expected a number, got: ~s" val)]))

(: arith-op : (Number Number -> Number) VAL VAL -> VAL)
;; gets a Racket numeric binary operator, and uses it within a NumV
;; wrapper
(define (arith-op op val1 val2)
  (NumV (op (NumV->number val1) (NumV->number val2))))

(: eval : CORE ENV -> VAL)
;; evaluates CORE expressions by reducing them to values
(define (eval expr env)
  (cases expr
    [(CNum n) (NumV n)]
    [(CAdd l r) (arith-op + (eval l env) (eval r env))]
    [(CSub l r) (arith-op - (eval l env) (eval r env))]
    [(CMul l r) (arith-op * (eval l env) (eval r env))]
    [(CDiv l r) (arith-op / (eval l env) (eval r env))]
    [(CRef pos) (list-ref env pos)]
    [(CFun bound-body) (FunV bound-body env)]
    [(CCall fun-expr arg-expr)
     (let ([fval (eval fun-expr env)])
       (cases fval
         [(FunV bound-body f-env)
          (eval bound-body (cons (eval arg-expr env) f-env))]
         [else (error 'eval "`call' expects a function, got: ~s" fval)]))]))

(: run : String -> Number)
;; evaluate a BRANG program contained in a string
(define (run str)
  (let ([result (eval (preprocess (parse str) de-empty-env) '())])
    (cases result
      [(NumV n) n]
      [else (error 'run "evaluation returned a non-number: ~s" result)])))

;; tests
(test (run "{call {fun {x} {+ x 1}} 4}")
      => 5)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {call add3 1}}")
      => 4)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {with {add1 {fun {x} {+ x 1}}}
                {with {x 3}
                  {call add1 {call add3 x}}}}}")
      => 7)
(test (run "{with {identity {fun {x} x}}
              {with {foo {fun {x} {+ x 1}}}
                {call {call identity foo} 123}}}")
      => 124)
(test (run "{with {x 3}
              {with {f {fun {y} {+ x y}}}
                {with {x 5}
                  {call f 4}}}}")
      => 7)
(test (run "{call {with {x 3}
                    {fun {y} {+ x y}}}
                  4}")
      => 7)
(test (run "{with {f {with {x 3} {fun {y} {+ x y}}}}
              {with {x 100}
                {call f 4}}}")
      => 7)
(test (run "{call {call {fun {x} {call x 1}}
                        {fun {x} {fun {y} {+ x y}}}}
                  123}")
      => 124)

(test (run "{call {fun {x} {- x 1}} 4}") => 3)
(test (run "{call {fun {x} {* x 2}} 4}") => 8)
(test (run "{call {fun {x} {/ x 2}} 4}") => 2)
(test (run "{call {fun {x y} {* x y}} 2 4}") => 8)

(test (run "{with {add {fun {x y} {+ x y}}} {call add 420 420}}") => 840)
(test (run "{with {add {fun {x y z} {+ x {+ y z}}}} {call add 420 420 420}}")
      => 1260)
(test (run "{with {mul {fun {x y} {* x y}}} {call mul 4 2}}") => 8)
(test (run (string-append "{with {mul {fun {x y z} {* x {call {fun {y z} "
                          "{* y z}} y z}}}} {call mul 2 3 4}}")) => 24)
(test (run "{with {sub {fun {x y} {- x y}}} {call sub 4 2}}") => 2)
(test (run "{with {sub {fun {x y} {- x y}}} {call sub 5 10}}") => -5)
(test (run "{with {div {fun {x y} {/ x y}}} {call div 6 2}}") => 3)
(test (run "{with {div {fun {x y} {/ x y}}} {call div 5 10}}") => 1/2)

(test (run "{with {x} x}")
      =error> "bad `with' syntax in (with (x) x)")
(test (run "{fun {} x}")
      =error> "bad `fun' syntax with 0 arguments in (fun () x)")
(test (run "{call {fun {x} } x}")
      =error> "bad `fun' syntax in (fun (x))")
(test (run "{call {fun {x} x}}")
      =error> "bad `call' syntax with missing arguments in (call (fun (x) x))")
(test (run "{}")
      =error> "bad syntax in ()")
(test (run "{call {fun {x} y} 420}")
      =error> "No mapping found for y")
(test (run "{* {fun {x} x} 420}")
      =error> "arith-op: expected a number")
(test (run "{call 420 420}")
      =error> "`call' expects a function")
(test (run "{fun {x} {+ x x}}")
      =error> "evaluation returned a non-number")

(define minutes-spent 630)