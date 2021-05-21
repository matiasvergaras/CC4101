#lang play
(print-only-errors #t)
(require "tarea1.rkt")
#| CC4101: Lenguajes de Programación
-- Tarea 1 Semestre Otoño 2021 (2021-1)
-- Alumno: Matías Vergara Silva
-- Script: tests pregunta 1: Tipos estáticos
|#

#| ======= TAREA 1: LENGUAJE CON FUNCIONES DE PRIMER ORDEN =======|#
#| -------  Tipos estáticos, tipos opcionales, contratos   -------|#
#| --------------  Test parte 2: Chequeo dinámico   --------------|#


#|------------------   Tests del enunciado   -----------------|#

(test (run '{ ;; Programa de Ejemplo 1
   {define {sum x y z} {+ x {+ y z}}}
   {define {max x y} {if {< x y} y x}}
   {with {{x 9}}
        {sum {max x 6} 2 -10} }
}) 1)

(test (run '{ ;; Programa de Ejemplo 2
   {with {{x 5} {y 7} {z 42}}
         z}
}) 42)

(test (run '{ ;; Programa de Ejemplo 3
   {define {triple x} {* 3 x}}
   {define {add2 x} {+ 2 x}}
   {add2 {triple 2}}
}) 8)


#|------------------   Tests personalizados   -----------------|#
#| Primero probaremos problemas con errores de tipo pero con
-- flag use-typecheck en falso, para asegurarnos que estamos
-- testeando solo lo relativo a la P1.
|#

;Programa con error de tipos en una función que no se usa.
(test (run '{
   {define {triple x} {* 3 #f}}
   {define {add2 x} {+ 2 x}}
   {add2 2}} '() #f) 4)

; Función con error de tipo en la condición del if
(test (run '{
   {define {iden x} {if {+ x x} x 0}}
   {iden 2}} '() #f) 2)

;Programa con error de tipos en un operador. Debe caerse en runtime.
(test/exn (run '{
  {define {badsum x y} {+ (! x) y}}
  {badsum 1 2}} '() #f )"Runtime type error: expected Boolean found Number")

;Lo mismo, pero con tipos declarados. No deben tener efecto.
(test/exn (run '{
  {define {badsum {x : Any} {y : Num}} : Num {+ (! x) y}}
  {badsum 1 2}} '() #f )"Runtime type error: expected Boolean found Number")

#| Confiaremos en que los tests anteriores demuestran que el typechecker
-- no nos molestará, y entraremos a testear las funcionalidades de la P1.
|#

;Buen comportamiento con casos simples: un solo numero
(test (run '{3} '() #f) 3)

;Buen comportamiento con casos simples: un solo boolean
(test (run '{#f} '() #f) #f)

;Buen comportamiento con casos simples: operacion binaria ilegal
(test/exn (run '{{+ 1 #f}} '() #f) "Runtime type error: expected Number found Boolean")

;Buen comportamiento con casos simples: operador +
(test (run '{{+ 1 2}} '() #f) 3) ;asumimos buen comportamiento para -, *, /
(test/exn (run '{{+ #t #t}} '() #f) "Runtime type error: expected Number found Boolean")



;Buen comportamiento con casos simples: operador >
(test (run '{{> 3 3}} '() #f) #f)
(test (run '{{> 3 2}} '() #f) #t)

;Buen comportamiento con casos simples: operador <
(test (run '{{< 3 3}} '() #f) #f)
(test (run '{{< 3 4}} '() #f) #t)

;Buen comportamiento con casos simples: operador &&
(test (run '{{< 3 3}} '() #f) #f)
(test (run '{{< 3 4}} '() #f) #t)

;Buen comportamiento con casos simples: operador <
(test (run '{{< 3 3}} '() #f) #f)
(test (run '{{< 3 4}} '() #f) #t)

;with en el cual se reestablece el valor de x.
;Debe entregar el primero de izqda a der.
(test (run '{ 
   {with {{x 12} {y 7} {z 42} {x 5}}
         x}
} '() #f) 12)

;with con expresiones anidadas
(test (run '{ 
   {with {{x {+ 1 2}} {y {! #f}} {z {* 0 5}} {w {/ 3 6}}}
         {if y (> (+ x z) x) z}}
   } '() #f) #f)

;with con expresiones anidadas y operacion en condicion
(test (run '{ 
   {with {{x {+ 1 2}} {y {! #f}} {z {* 0 5}} {w {/ 3 6}}}
         {if (! y) (> (+ x z) x) {* z z}}}
   } '() #f) 0)

;with que usa una funcion numerica como expresion de un valor
(test (run '{
   {define {triple x} {* 3 x}}
   {define {not x} {! x}}
   {with {{x {triple 2}} {y {! {> 2 {triple 1}}}} }
         {if y x 0}}
   } '() #f) 6) 

;with que usa una funcion booleana como expresion de un valor y
;expresiones anidada en la definicion de funciones
(test (run '{
   {define {same x y} {= x y}}
   {define {first-quadrant x y} {&& {> x 0}{> y 0}}}
   {with {{x 1} {y 2} {w (first-quadrant 1 -1)}}
         {if w (same x y) (first-quadrant x y)}}
   } '() #f) #t) 

;mismo test, cambiando nand por nor (para probar || y =)
(test (run '{
   {define {same x y} {= x y}}
   {define {nand x y}  {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (+ x y)}}
   } '() #f) #f)

;mismo test, forzando error: operador = entre num y bool
(test/exn (run '{
   {define {same x y} {= x y}}
   {define {nand x y} {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same #t y) (nand x y)}}
   } '() #f) "Runtime type error: expected Number found Boolean")

;mismo test, forzando error: operador || entre numeros (nand 1 2)
(test/exn (run '{
   {define {same x y} {= x y}}
   {define {nand x y} {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand 1 2)}}
         {if w (same x y) (+ x y)}}
   } '() #f) "Runtime type error: expected Boolean found Number")

;aplicacion anidada de funciones con multiples argumentos
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x y} {+ x 3}}
   {with {{x 1} {y 2}}
         {restsqrt (sum3 x y) y}}
   } '() #f) 12)

;aplicacion anidada de funciones con multiples argumentos
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x y} {+ x 3}}
   {with {{x 1} {y 2}}
         {restsqrt (sum3 x y) y}}
   } '() #f) 12)

;aplicacion anidada de funciones con multiples argumentos
;sin with de por medio
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x} {+ x 3}}
   {restsqrt (sum3 1) 2}}
    '() #f) 12)

;aplicacion anidada de funciones con multiples argumentos
;con with anidado
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x} {+ x 3}}
   {restsqrt (sum3 {with {{w 4}} w}) 2}}
    '() #f) 45)

;aplicacion anidada de funciones con multiples argumentos
;con with anidado (y con error de tipos). 
(test/exn (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x} {+ x 3}}
   {restsqrt (sum3 {with {{w {+ 1 #t}}} w}) 2}}
    '() #f) "Runtime type error: expected Number found Boolean")

;funcion recursiva, definida en base a if
(test (run '{
   {define {sub1until0 x} {if (= x 0) x (sub1until0 (sub1 x))}}
     {sub1until0 5}} '() #f) 0)

;misma funcion recursiva, pero se debe caer en el caso base
(test/exn (run '{
   {define {sub1until0 x} {if (= 0 (= x 0)) x (sub1until0 (sub1 x))}}
     {sub1until0 5}} '() #f) "Runtime type error: expected Number found Boolean")

;misma funcion recursiva, pero introduciendo x con with
(test (run '{
   {define {sub1until0 x} {if  (= x 0) x (sub1until0 (sub1 x))}}
     {with {{x 1}} {sub1until0 x}}} '() #f) 0)

;funciones definidas + with + tipos (no tienen efecto)
(test (run '{
   {define {same {x : Num} {y : Num}} : Num {= x y}}
   {define {nand {x : Any} {y : Any}} : Num {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   } '() #f) #f)

;|========================================================================|
;| Notese que en el ejemplo anterior el caso falso  (nand x y)            |
;| del if incluye un error de tipo, pues hace && de 1 y 2. Sin embargo,   |
;| como w se evalua a #t, el intérprete no llega a evaluar dicho caso     |
;| y por ende no se falla en ejecución(pues estamos en chequeo dinámico). |
;|========================================================================|