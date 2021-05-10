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
#| --------------  Test parte 1: Chequeo dinámico   --------------|#



#|------------------   Tests del enunciado  -----------------

(test (run '{{with {{x : Num 5} {y : Num 10}} {+ x y}}} '() #t) 15)

(test (run '{{define {gt42 x} : Bool {> x 42}}
 {gt42 43}} '() #t) #t)

(test (run '{{define {id {x : Num}} x}
 {id 5}} '() #t) 5)

(test/exn (run '{{define {add2 {x : Num}} {+ x 2}}
 {with {{oops #f}}
   {add2 oops}}} '() #t) "Runtime type error")

(test (typecheck '{3}) 'Num)

(test (typecheck '{{define {f {p : Bool}} {&& p {! p}}}
                          {f {> 3 4}}}) 'Any)

(test/exn (typecheck '{{define {one {x : Num}} 1}
                          {one #t}}) "Static type error: expected Num found Bool")

(test/exn (typecheck '{{> 10 #t}})
  "Static type error: expected Num found Bool")

(test/exn (typecheck '{{if 73 #t #t}})
  "Static type error: expected Bool found Num")

(test/exn (typecheck '{{with {{x 5} {y : Num #t} {z 42}}
                            z}})
  "Static type error: expected Num found Bool")


#|------------------   Tests personalizados   -----------------|#
-- usaremos los mismos tests de la P1, pero variando la declaracion
-- de tipos.
|#


;Programa con error de tipos en una función que no se usa.
;Sin declarar tipos.
(test/exn (run '{
   {define {triple x} {* 3 #f}}
   {define {add2 x} {+ 2 x}}
   {add2 2}} '() #t) "Static type error: expected Num found Bool")


;Programa con error de tipos en una función que no se usa.
;Declarando tipo de la función (no debería dejar pasar el problema).
(test/exn (run '{
   {define {triple {x : Any}} : Any {* 3 #f}}
   {define {add2 x} {+ 2 x}}
   {add2 2}} '() #t) "Static type error: expected Num found Bool")


;Programa con error de tipos en una función que se usa en if
;Declarando tipo de la función como Any (debería pasar por comodín)
(test (run '{
   {define {add2 x} : Any {+ 2 x}}
   {if (add2 1) 2 0}} '() #t) 2)

;Programa con error de tipos en una función que se usa en if
;Declarando tipo de la función como Num (debería caerse en typecheck)
(test/exn (run '{
   {define {add2 x} : Num {+ 2 x}}
   {if (add2 1) 2 0}} '() #t) "Static type error: expected Bool found Num")

;Programa con error de tipo en argumento declarado como Num
(test/exn (run '{
   {define {negate {x : Bool}} : Bool {! x}}
   {negate 1}} '() #t) "Static type error: expected Bool found Num")

;Programa con error de tipo entre cuerpo de función y tipo declarado
(test/exn (run '{
   {define {negate {x : Bool}} : Num {! x}}
   {negate #t}} '() #t) "Static type error: expected Bool found Num")



;Programa con error de tipos en un operador.
(test/exn (run '{
  {define {badsum x y} {+ (! x) y}}
  {badsum 1 2}} '() #t ) "Static type error: expected Bool found Num")


;Lo mismo, pero con tipos declarados. No deben tener efecto.
(test/exn (run '{
  {define {badsum {x : Any} {y : Num}} : Num {+ (! x) y}}
  {badsum 1 2}} '() #t ) "Static type error: expected Bool found Num")

;Buen comportamiento con casos simples
(test/exn (run '{{+ 1 #f}} '() #t) "Static type error: expected Num found Bool")


;Buen comportamiento del typechecker con casos simples
(test (typecheck '{{+ 1 2}}) 'Num)

;Buen comportamiento del typechecker con casos simples
(test (typecheck '{3}) 'Num)

;Buen comportamiento del typechecker con casos simples
(test (typecheck '{#f}) 'Bool)

;with en el cual se reestablece el tipo y valor de x.
;El tipo entregado debe concordar con el x de mas a la izqda.
(test (typecheck
       '{{with {{x : Num 12} {y : Num 7} {z : Num 42} {x : Any 5}}
         x}}) 'Num)

;Mismo ejemplo anterior, pero preguntando por el tipo de un elemento
;que no es el primero.
(test (typecheck
       '{{with {{x : Num 12} {y : Num 7} {z : Num 42} {x : Any 5}}
         z}}) 'Num)

;with con expresiones recursivas
;asignando todos los tipos de forma correcta
;debe fallar ya que los casos del if son Bool y Num.
(test/exn (run '{ 
   {with {{x : Number {+ 1 2}} {y : Bool {! #f}} {z : Num {* 0 5}} {w : Num {/ 3 6}}}
         {if y (> (+ x z) x) z}}
   } '() #t) "Static type error: expected Bool found Num") 


;mismo ejemplo, pero cambiando el caso Bool del if a Num.
(test (run '{ 
   {with {{x : Number {+ 1 2}} {y : Bool {! #f}} {z : Num {* 0 5}} {w : Num {/ 3 6}}}
         {if y 1 z}}
   } '() #t) 1)
(test (typecheck '{
         {with {{x : Number {+ 1 2}} {y : Bool {! #f}} {z : Num {* 0 5}} {w : Num {/ 3 6}}}
         {if y 1 z}}
   }) 'Num)

;mismo ejemplo, pero cambiando el caso Num del if a Bool.
(test (run '{ 
   {with {{x : Number {+ 1 2}} {y : Bool {! #f}} {z : Num {* 0 5}} {w : Num {/ 3 6}}}
         {if y (> (+ x z) x) #t}}
   } '() #t) #f) 
(test (typecheck '{
         {with {{x : Number {+ 1 2}} {y : Bool {! #f}} {z : Num {* 0 5}} {w : Num {/ 3 6}}}
         {if y (> (+ x z) x) #t}}
   }) 'Bool)


;with con expresiones recursivas y operacion en condicion
(test (run '{ 
   {with {{x : Num {+ 1 2}} {y : Any {! #f}} {z : Num {* 0 5}} {w : Any {/ 3 6}}}
         {if (! y) (> (+ x z) x) {* z z}}}
   } '() #f) 0)

;mismo ejemplo, pero generando un error en la definición recursiva
;de y con respecto al tipo declarado
(test/exn (run '{ 
   {with {{x : Num {+ 1 2}} {y : Num {! #f}} {z : Bool {* 0 5}} {w : Any {/ 3 6}}}
         {if (! y) (> (+ x z) x) {* z z}}}
   } '() #t) "Static type error")


#|
;with que usa una funcion numerica como expresion de un valor
(test (run '{
   {define {triple x} {* 3 x}}
   {define {not x} {! x}}
   {with {{x {triple 2}} {y {! {> 2 {triple 1}}}} }
         {if y x 0}}
   } '() #f) 6) 

;with que usa una funcion booleana como expresion de un valor y
;expresiones recursivas en la definicion de funciones
(test (run '{
   {define {same x y} {= x y}}
   {define {nand x y} {&& {! x}{! y}}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (+ x y)}}
   } '() #f) 3) 

;mismo test, cambiando nand por nor (para probar || y =)
(test (run '{
   {define {same x y} {= x y}}
   {define {nand x y} {|| {! x}{! y}}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (+ x y)}}
   } '() #f) #f)

;mismo test, forzando error: operador = entre num y bool
(test/exn (run '{
   {define {same x y} {= x y}}
   {define {nand x y} {|| {! x}{! y}}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same #t y) (+ x y)}}
   } '() #f) "Runtime type error: expected Number found Boolean")

;mismo test, forzando error: operador && entre num y bool
;esto no se cae en esta parte ya que racket acepta el and
;entre num y bool.
(test (run '{
   {define {same x y} {= x y}}
   {define {nand x y} {|| {! x}{! y}}}
   {with {{x 1} {y 2} {z #t} {w (nand 1 2)}}
         {if w (same x y) (+ x y)}}
   } '() #f) 3)

;aplicacion recursiva de funciones con multiples argumentos
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x y} {+ x 3}}
   {with {{x 1} {y 2}}
         {restsqrt (sum3 x y) y}}
   } '() #f) 12)

;aplicacion recursiva de funciones con multiples argumentos
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x y} {+ x 3}}
   {with {{x 1} {y 2}}
         {restsqrt (sum3 x y) y}}
   } '() #f) 12)

;aplicacion recursiva de funciones con multiples argumentos
;sin with de por medio
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x} {+ x 3}}
   {restsqrt (sum3 1) 2}}
    '() #f) 12)

;aplicacion recursiva de funciones con multiples argumentos
;con with anidado
(test (run '{
   {define {restsqrt x y} {- (* x x) (* y y)}}
   {define {sum3 x} {+ x 3}}
   {restsqrt (sum3 {with {{w 4}} w}) 2}}
    '() #f) 45)

;aplicacion recursiva de funciones con multiples argumentos
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

|#