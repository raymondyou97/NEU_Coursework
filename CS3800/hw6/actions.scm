;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Action procedures called by the parser.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (empty) '())
  
(define (identity x) x)

(define (mkInput I P)
  (list 'input I P))

(define (mkOutput E)
  (list (list 'output E)))

(define (mkAccept)
  '(accept))

(define (mkReject)
  '(reject))

(define (mkSkip)
  '(skip))

(define (mkAssign I E)
  (list 'assign I E))

(define (mkIf B S1 S2)
  (list 'if B S1 S2))

(define (mkWhile B S)
  (list 'while B S))

(define (mkSequence Q)
  (list 'sequence Q))

(define (mkFork I E1 E2)
  (list 'fork I E1 E2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (none? ast) (eq? ast (mkNone)))

(define (mkNone) #f)

(define (mkPartial <op> <exp> <rest>)
  (list 'partial <op> <exp> <rest>))

(define (partialOp p)
  (assert (and 'partialOp (eq? 'partial (car p))))
  (cadr p))

(define (partialExp p)
  (assert (and 'partialExp (eq? 'partial (car p))))
  (caddr p))

(define (partialRest p)
  (assert (and 'partialRest (eq? 'partial (car p))))
  (cadddr p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (mkPartialAdd T E2)
  (list 'partial '+ T E2))

(define (mkPartialSub T E2)
  (list 'partial '- T E2))

(define (mkPartialMul F T2)
  (list 'partial '* F T2))

(define (mkPartialDiv F T2)
  (list 'partial '/ F T2))

(define (mkPartialLT E)
  (list 'partial '< E (mkNone)))

(define (mkPartialEQ E)
  (list 'partial '= E (mkNone)))

(define (mkPartialGT E)
  (list 'partial '> E (mkNone)))

;;; Rotations needed here to compensate for conversion into LL(1) form.

(define (mkExp T E2)
  (if (none? E2)
      T
      (list (partialOp E2) T (partialExp E2))))

(define (mkTerm F T2)
  (if (none? T2)
      F
      (list (partialOp T2) F (partialExp T2))))

(define (mkBoolExp E B2)
  (list (partialOp B2) E (partialExp B2)))

;;; End of rotations.

(define (mkNot B)
  (list 'not B))

(define (mkNum)
  (list 'num
        (string->number tokenValue)))

(define (mkVar)
  (list 'var (string->symbol tokenValue)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Error procedure called by the parser.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
(define (parse-error nonterminal expected-terminals)
  (let* ((culprit (next-token))
         (culprit-as-string (symbol->string culprit))
         (culprit-as-string
          (if (memq culprit expected-terminals)
              (string-append "illegal " culprit-as-string)
              culprit-as-string))
         (msg (string-append
               "Syntax error in line "
               (number->string (+ 1 (port-lines-read input-port)))
               " while parsing "
               (symbol->string nonterminal)
               (string #\newline)
               "  Encountered "
               culprit-as-string
               " while expecting "
               (case nonterminal
                 ((<datum> <outermost-datum> <data>)
                  "a datum")
                 (else
                  (string-append
                   (string #\newline)
                   "  "
                   (apply string-append
                          (map (lambda (terminal)
                                 (string-append " "
                                                (symbol->string terminal)))
                               expected-terminals)))))
               (string #\newline))))
    (display msg)
    (newline)
    (write culprit-as-string)
    (newline)
    (write input-port)
    (newline)
    (error msg culprit-as-string input-port)))

