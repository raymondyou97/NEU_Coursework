;;; Given a string of ASCII characters,
;;; returns its encoding as an integer.

(define (string->integer s)
  (do ((i 0 (+ i 1))
       (n 0 (+ (* 256 n) (char->integer (string-ref s i)))))
      ((= i (string-length s))
       n)))
