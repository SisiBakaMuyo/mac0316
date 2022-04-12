#lang scheme

;Luis Vitor Zerkowski - 9837201
;Isis Ardisson Logullo - 7577410

(require racket/stream)

(define itera (lambda (f x)
                (stream-cons x (itera f (f x)))
              )
)
;Examples
;(stream-first (itera (lambda (x) (+ 1 x)) 1))
;(stream-first (stream-rest (itera (lambda (x) (+ 1 x)) 1)))


(define ciclo (lambda (l)
                (stream-cons l (ciclo l))
              )
)
;Examples
;(stream-first (stream-first (ciclo (itera (lambda (x) (+ 1 x)) 1))))
;(stream-first (stream-rest (stream-first (ciclo (itera (lambda (x) (+ 1 x)) 1)))))


(define (fib)
  (letrec ((proximo (lambda (x y)
                          (stream-cons x (proximo y (+ x y)))
                        )))
    (proximo 1 1)
  )
)
;Examples
;(fib)
;(stream-first (fib))
;(stream-first (stream-rest (stream-rest (fib))))


(define merge (lambda (l1 l2)
                (stream-cons (stream-first l1) (merge l2 (stream-rest l1)))
              )
)
;Examples
;(stream-first (merge (itera (lambda (x) (+ 1 x)) 1) (itera (lambda (x) (+ 1 x)) 2)))
;(stream-first (stream-rest (merge (itera (lambda (x) (+ 1 x)) 1) (itera (lambda (x) (+ 1 x)) 2))))
;(stream-first (stream-rest (stream-rest (merge (itera (lambda (x) (+ 1 x)) 1) (itera (lambda (x) (+ 1 x)) 2)))))


(define foreach-inf (lambda (lista f)
                  (if (null? lista) '()
                      (stream-cons (f (stream-first lista)) (foreach-inf (stream-rest lista) f))
                  )
                )
)
;Examples
;(stream-first (foreach-inf '(1 2 3) (lambda (x) (+ 1 x))))
;(stream-first (stream-rest (foreach-inf '(1 2 3) (lambda (x) (+ 1 x)))))
;(stream-first (stream-rest (foreach-inf (itera (lambda (x) (+ 1 x)) 1) (lambda (x) (+ 1 x)))))