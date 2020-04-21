;;; Implementation of abstract syntax trees for While/Fork.

;;; Given an abstract syntax tree, tells what kind of tree it is.

(define kind car)

(define input.var cadr)
(define input.pgm caddr)

(define output.exp cadr)

(define assign.lhs cadr)
(define assign.rhs caddr)

(define if.test cadr)
(define if.then caddr)
(define if.else cadddr)

(define while.test cadr)
(define while.body caddr)

(define sequence.stms cadr)

(define fork.var cadr)
(define fork.exp1 caddr)
(define fork.exp2 cadddr)

(define exp.left cadr)
(define exp.right caddr)

(define not.exp cadr)

(define num.val cadr)

(define var.name cadr)

