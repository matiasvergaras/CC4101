#lang play
(require "main-V2.rkt")
(print-only-errors)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                 TESTS BASE                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (run-val '(+ 1 2)) 3)
(test (run-val '(< 1 2)) #t)
(test (run-val '(- 2 1)) 1)
(test (run-val '(* 2 3)) 6)
(test (run-val '(= (+ 2 1) (- 4 1))) #t)
(test (run-val '(and #t #f)) #f)
(test (run-val '(or #t #f)) #t)
(test (run-val '(not (not #t))) #t)
(test (run-val '(if (not #f) (+ 2 1) 4)) 3)
(test (run-val '(local ([define x 5])
              (seqn {+ x 1}
                    x))) 5)

;; Ejemplos del enunciado
(test (run-val '(local
              [(define o (object
                          (field x 1)
                          (field y 2)
                          (method sum (z) (+ (get x) (+ (get y) z)))
                          (method set-x (val) (set x val))
                          (method get-y () (get y))))]
            (seqn
             (send o set-x (+ 1 3))
             (+ (send o sum 3) (send o get-y)))))
      11)

(test (run-val
       '(local
            [(define a
               (object
                (method auto-apply (o)
                        (send o apply o))
                (method foo () 5)
                ))
             (define o (send a auto-apply
                             (object
                              (method apply (other) (send other apply2 this))
                              (method apply2 (other) this)
                              (method foo () 42))))]
          (send o foo)))
      42)

(test (run-val '(local
              [(define smart-computer (object
                                       (method secret? (something) 42)))
               (define everything (object))
               (define oracle (object : smart-computer))]
               (send oracle secret? everything)))
      42)

(test (run-val '(local
              [(define seller (object
                               (method multiplier () 1)
                               (method price (item-number)
                                       (* item-number (send this multiplier)))))
               (define broker (object : seller
                                      (method multiplier () 2)))]
               (send broker price 3)))
      6)

(test (run-val '(local
                    ([define x (object
                                (field z 3)
                                (method get () (get z)))]
                     [define y (object : x)])
                  (send y get)))
      3)

(test/exn (run-val '(local
                        ([define x (object
                                    (field z 3)
                                    (method get () (get z)))]
                         [define y (object
                                    : x
                                    (method get () (get z)))])
                      (send y get)))
          "field not found")

;; A simple monotone counter
(define counter '(object
                  (field count 0)
                  (method incr () (set count (+ 1 (get count))))
                  (method get () (get count))))

(define (incrs-multiply x y)
  `(seqn
    (send ,y incr)
    (seqn
     (send ,x incr)
     (seqn
      (send ,x incr)
      (* (send ,x get) (send ,y get))
      ))))

(test (run-val
       `(local ([define c ,counter])
          (seqn (send c incr)
                (local ([define c2 (shallow-copy c)])
                  ,(incrs-multiply 'c 'c2)))))
      6)

(test (run-val
       `(local ([define c (object : ,counter)])
          (seqn (send c incr)
                (local ([define c2 (shallow-copy c)])
                  ,(incrs-multiply 'c 'c2)))))
      16)

(test (run-val
       `(local ([define c (object : ,counter)])
          (seqn (send c incr)
                (local ([define c2 (deep-copy c)])
                  ,(incrs-multiply 'c 'c2)))))
      6)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                  SUS TESTS                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                  SUS TESTS                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;test para modificar un campo
(test (run-val '(local
                  [(define o (object
                              (field g (+ 2 3))
                              (method getg () (get g))
                              (method setg () (set g 10))))]
                  (seqn (send o setg)
                        (send o getg))))
      10)

;;test para un send con mas de un argumento
(test (run-val '(local
                  [(define o (object
                              (field x 3)
                              (field g (+ 2 (get x)))
                              (method sum (y z) (+ y (+ z (get g))))))]
                   (send o sum 10 5)))
      20)

;;
(test/exn (run-val '(local
                  [(define o (object
                              (field g (+ 2 3))
                              (method getg () g)
                              (method setg () (set g 10))))]
                  (seqn (send o setg)
                        (send o getg))))
      "free identifier")

;; test manejo correcto del this y separación de métodos con el mismo nombre pero en distintos objetos
(test (run-val '(local
              [(define o (object
                          (field y (object (field x 3)
                                           (method sum (x) (+ x (send this getx )))
                                           (method getx () (get x))))
                          (field z 5)
                          (method sum (z) (+ z (+ (send this gety) (get z))))
                          (method gety () (send (get y) getx)))
                 
                 )]
              (send o sum 3)))
      11)


;;test del correcto manejo del this sin delegacion, además de la correcta separación entre variables
;; (+ (send (get y) sum y) el primer "y" en get llama a objeto, mientras que el segundo al valor que se le asocia
;; en el metodo suma de o.
(test (run-val '(local
              [(define o (object
                          (field y (object (field x 3)
                                           (method sum (x) (+ x (send this getx )))
                                           (method getx () (get x))))
                          (field z 2)
                          (method sum (z y) (+ z (+ (send (get y) sum y) (get z)))))
                 )]
              (send o sum 5 4)))
14)

;;test para ver que un objeto entienda solo sus campos

(test/exn (run-val '(local [(define o (object
                              (field x 3)
                              (field g (+ 2 (get x)))
                              (method sum (y z) (+ y (+ z (get p))))))]
           (send o sum 2 3)))
           "field not found")

(test/exn (run-val '(local [(define p (object (field p 2)))
                            (define o (object
                              (field x 3)
                              (field g (+ 2 (get x)))
                              (method sum (y z) (+ y (+ z (get p))))))]
           (send o sum 2 3)))
           "field not found")

;;test para ver que un objeto entienda solo sus metodos

(test/exn (run-val '(local [(define o (object
                              (field x 3)
                              (field g (+ 2 (get x)))
                              (method sum (y z) (+ y (+ z (get p))))))]
           (send o mul 2 3)))
           "method not found")


(test/exn (run-val '(local [(define p
                              (object
                               (field p 2)
                               (method mul (x y) (* x y))))
                            (define o
                              (object
                              (field x 3)
                              (field g (+ 2 (get x)))
                              (method sum (y z) (+ y (+ z (get p))))))]
           (send o mul 2 3)))
           "method not found")


;;test para el uso de this solo dentro del objeto

(test/exn (run-val '(local [(define p
                              (object
                               (field p 2)
                               (method mul (x y) (* x y))))
                            (define o
                              (object
                              (field x 3)
                              (field g (+ 2 (get x)))
                              (method sum (y z) (+ y (+ z (get p))))))]
           (send this mul 2 3)))
           "this used outside of an object")

;;test para el uso de get solo dentro del objeto

(test/exn (run-val '(local [(define o
                              (object
                               (field x 3)
                               (field g (+ 2 (get x)))
                               (method sum (y z) (+ y (+ z (get p))))))]
           (get p)))
           "get used outside of an object")

;;test para el uso de set solo dentro del objeto

(test/exn (run-val '(local [(define o
                              (object
                              (field x 3)
                              (field g (+ 2 (get x)))
                              (method sum (y z) (+ y (+ z (get p))))))]
           (set p 2)))
           "set used outside of an object")

;;test de delegacion
(test (run-val '(local
                    ([define o (object
                                (field f 10)
                                (method sum () (+ (get f) (send this getj))))]
                     [define y (object : o
                                       (field j 2)
                                       (method getj () (get j)))])
                  (send y sum)))
      12)



;;test de delegacion triple, para ver que get trabaje en el objeto en el que está
;; y para llamada de un this desde un método de un objeto al que se le delegó un mensaje
(test (run-val '(local
                  [(define x (object
                              (field w 3)
                              (method sum () (+ (send this getj) (get w)))))
                   
                   (define o (object : x
                                     (field f 10)
                                     (method del () (+ (get f) (* (send this getj) (send o sum))))))
                   (define y (object : o
                                     (field j 2)
                                     (method getj () (get j))))]
                  (send y del)))
      20)


;;test de delegacion para ver que set trabaje en el objeto en el que está

(test (run-val '(local
                    ([define o (object
                                (field f 10)
                                (method setf (a) (set f a)))]
                     [define y (object : o
                                       (field f 2)
                                       (method getf () (get f)))])
                  (seqn (send y setf 9)
                  (send y getf))))
      2)

;;test para comprobar que un objeto y su shallow-copy delegan al mismo objeto

(test (run-val '(local
                    ([define o (object
                                (field f 10)
                                (method setf (a) (set f a))
                                (method getf () (get f)))]
                     [define y (object : o
                                       (field f 2)
                                       (method setfo () (send o setf 3))
                                       )]
                     [define z (shallow-copy y)])
                  (seqn
                   (send z setfo)
                   (send y getf))))
      3)

;;test para comprobar que un objeto y su deep-copy delegan a objetos distintos

(test (run-val '(local
                    ([define o (object
                                (field f 10)
                                (method setf (a) (set f a))
                                (method getf () (get f)))]
                     [define y (object : o
                                       (field f 2)
                                       (method setfo () (send o setf 3))
                                       )]
                     [define z (deep-copy y)])
                  (seqn
                   (send y setfo)
                   (send z getf))))
      10)

;;test para lambdas como objetos
(test (run-val '(local
              [(define f (fun (x)
                              (+ x x)))]
              (f 5)))
10)

(test (run-val '(local
                  [(define j (fun (x y z)
                                  (+ x (* y z))))]
                  (j 2 3 10)))

      32)