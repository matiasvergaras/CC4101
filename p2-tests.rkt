#lang play
(print-only-errors #t)
(require "tarea1.rkt")
#| CC4101: Lenguajes de Programación
-- Tarea 1 Semestre Otoño 2021 (2021-1)
-- Alumno: Matías Vergara Silva
-- Script: tests pregunta 2: Tipos dinámicos
|#

#| ======= TAREA 1: LENGUAJE CON FUNCIONES DE PRIMER ORDEN =======|#
#| -------  Tipos estáticos, tipos opcionales, contratos   -------|#
#| --------------  Test parte 2: Tipos estáticos    --------------|#


#|------------------   Tests del enunciado  -----------------|#

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
;-- usaremos los mismos tests de la P1, pero variando la declaraciont
;-- de tipos.


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
;obs: (! x) pasa porque a x no se le declara tipo y racket acepta la negación de números.
(test/exn (run '{
  {define {badsum x y} {+ (! x) y}}
  {badsum 1 2}} '() #t ) "Static type error: expected Num found Bool")


;Lo mismo, pero declarando x como Num. debe caerse por la obs. anterior.
(test/exn (run '{
  {define {badsum {x : Num} {y : Num}} : Num {+ (! x) y}}
  {badsum 3 2}} '() #t ) "Static type error: expected Bool found Num")

;Lo mismo, pero declarando x como Bool e introduciéndolo con with como Num.
;También quitamos el error de (+ (! x) y) (bool como param de +) porque
;se detecta antes y no deja testear lo que buscamos.
;debe caerse por la obs. anterior.
(test/exn (run '{
  {define {badsum {x : Bool} {y : Num}} : Num {+ 1 y}}
  {with {{x : Num 3}{y : Num 2}} {badsum x y}}} '() #t ) "Static type error: expected Bool found Num")

;Buen comportamiento con casos simples
(test/exn (run '{{+ 1 #f}} '() #t) "Static type error: expected Num found Bool")


;Buen comportamiento del typechecker con casos simples
(test (typecheck '{{+ 1 2}}) 'Num)

;Buen comportamiento del typechecker con casos simples
(test (typecheck '{3}) 'Num)

;Buen comportamiento del typechecker con casos simples
(test (typecheck '{#f}) 'Bool)

;Buen comportamiento del typechecker con casos simples
(test (typecheck '{{&& #f #t}}) 'Bool)

;Buen comportamiento del typechecker con casos simples
(test (typecheck '{{|| #f #t}}) 'Bool)

;Buen comportamiento del typechecker con casos simples
(test/exn (typecheck '{{|| 1 #t}}) "Static type error: expected Bool found Num")

;para revisar que una definicion de funcion no sobreescriba a la otra
(test (run '{{define {double {x : Num}} {+ x x}}
         {define {triple {x : Num}}
           {+ {+ x x} x}}
 {double 25}} '() #t) 50)

; lo mismo pero en el orden inverso (la funcion buscada es la ultima en
; guardar x)
(test (run '{{define {double {x : Num}} {+ x x}}
         {define {triple {x : Num}}
           {+ {+ x x} x}}
 {triple 25}} '() #f) 75)

;with en el cual se asigna x Any y se usa en &&.
;Typechecker debe respetar tipo estricto del operador (Bool).
(test (typecheck
       '{{with {{x : Any #t} {y : Any #f}}
         {&& x y}}}) 'Bool)

;mismo ejemplo anterior pero con || en lugar de &&
(test (typecheck
       '{{with {{x : Any #t} {y : Any #f}}
         {|| x y}}}) 'Bool)

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
;las ramas del if tienen tipo distinto (Bool y Num). Debe fallar en tipeo.
(test/exn (run '{ 
   {with {{x : Num {+ 1 2}} {y : Any {! #f}} {z : Num {* 0 5}} {w : Any {/ 3 6}}}
         {if (! y) (> (+ x z) x) {* z z}}}
   } '() #t) "Static type error: expected Bool found Num")

;mismo ejemplo, pero generando un error en la definición recursiva
;de y con respecto al tipo declarado
(test/exn (run '{ 
   {with {{x : Num {+ 1 2}} {y : Num {! #f}} {z : Bool {* 0 5}} {w : Any {/ 3 6}}}
         {if (! y) (> (+ x z) x) {* z z}}}
   } '() #t) "Static type error")

;usando una función con más argumentos de los que le corresponden
(test/exn (run '{
   {define {same x y} {= x y}}
   {with {{x 10} {y 5} {z 2} {w #t}}
         {if w (same x y x) (same x y)}}
   } '() #t) "Static type error: arity mismatch - expected 2 arguments but received 3")



;with que usa una funcion numerica como expresion de un valor
(test (run '{
   {define {triple x} {* 3 x}}
   {define {not x} {! x}}
   {with {{x {triple 2}} {y {! {> 2 {triple 1}}}} }
         {if y x 0}}
   } '() #t) 6)
(test (typecheck '{                
   {define {triple x} {* 3 x}}
   {define {not x} {! x}}
   {with {{x {triple 2}} {y {! {> 2 {triple 1}}}} }
         {if y x 0}}
   }) 'Any)

;mismo programa pero ahora declarando los tipos para lograr que
;typecheck no devuelva Any si no Num
(test (typecheck '{                
   {define {triple {x : Num}} : Num {* 3 x}}
   {define {not {x : Bool}} : Bool {! x}}
   {with {{x : Num {triple 2}} {y : Bool {! {> 2 {triple 1}}}} }
         {if y x 0}}
   }) 'Num)

;with que usa una funcion booleana como expresion de un valor y
;expresiones recursivas en la definicion de funciones.
(test (run '{
   {define {same {x : Num} {y : Num}} {= x y}}
   {define {nand {x : Any} {y : Any}} {! (&& x y)}}
   {with {{x #t} {y #t} {z #t} {w (nand #f #t)}}
         {if w (same 1 2) (nand x y)}}
   } '() #t) #f)

(test (typecheck '{
   {define {same {x : Num} {y : Num}} {= x y}}
   {define {nand {x : Any} {y : Any}} {! (&& x y)}}
   {with {{x #t} {y #t} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   }) 'Any)




;mismo ejemplo anterior, sin problemas en declaracion de same y nand,
;pero pasando numeros en x e y. Debe caerse en runtime por la aplicación de nand,
;que forzaremos aplicando ! a w (para obtener #t en la condicion del if).
(test/exn (run '{
   {define {same {x : Num} {y : Num}} : Any {= x y}}
   {define {nand {x : Any} {y : Any}} : Any {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if (! w) (same x y) (nand x y)}}
   } '() #t) "Runtime type error: expected Boolean found Number")




;mismo ejemplo anterior, sin error de tipos en x e y,
;y declarando tipo de same y nand como Any para que
;run retorne y typecheck arroje 'Any
(test (run '{
   {define {same {x : Num} {y : Num}} : Any {= x y}}
   {define {nand {x : Any} {y : Any}} : Any {! (&& x y)}}
   {with {{x #t} {y #t} {z #t} {w (nand #t #t)}}
         {if w (same x y) #f}}
   } '() #t) #f)

(test (typecheck '{
   {define {same {x : Num} {y : Num}} : Any {= x y}}
   {define {nand {x : Any} {y : Any}} : Any  {! (&& x y)}}
   {with {{x #t} {y #t} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   })  'Any)

;mismo ejemplo anterior, pero declaramos tipo de same y nand como Bool
;(consistente con el cuerpo, debe incidir retorno de typecheck)
(test (run '{
   {define {same {x : Num} {y : Num}} : Bool {= x y}}
   {define {nand {x : Any} {y : Any}} : Bool  {! (&& x y)}}
   {with {{x 1} {y 1} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   } '() #t) #t)

(test (typecheck '{
   {define {same {x : Num} {y : Num}} : Bool {= x y}}
   {define {nand {x : Any} {y : Any}} : Bool  {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   }) 'Bool)


;aplicacion anidada de funciones con multiples argumentos
;sin with de por medio
;typecheck debe dar 'Num aunque sum se defina como Any pues
;los operadores binarios tienen tipo estricto
(test (run '{
   {define {restsqrt (x : Num) (y : Num)} : Num {- (* x x) (* y y)}}
   {define {sum3 (x : Num)} : Any {+ x 3}}
   {restsqrt (sum3 1) 2}}
    '() #t) 12)
(test (typecheck '{
   {define {restsqrt (x : Num) (y : Num)} : Num {- (* x x) (* y y)}}
   {define {sum3 (x : Num)} : Any {+ x 3}}
   {restsqrt (sum3 1) 2}}
   ) 'Num)

;funcion recursiva, definida en base a if.
(test (run '{
   {define {sub1until0 (x : Any)} : Num {if (= x 0) x (sub1until0 (sub1 x))}}
     {sub1until0 5}} '() #t) 0)

(test (typecheck  '{
   {define {sub1until0 (x : Any)} : Num {if (= x 0) x (sub1until0 (sub1 x))}}
     {sub1until0 5}}) 'Num)


;funciones definidas + with + tipos errados en la definición de funciones
;con respecto al tipo del cuerpo de las mismas
(test/exn (run '{
   {define {same {x : Num} {y : Num}} : Num {= x y}}
   {define {nand {x : Any} {y : Any}} : Num {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   } '() #t) "Static type error: expected Bool found Num")


;|========================================================================|
;| EJEMPLO FINAL DE LA PARTE 1 - ahora con chequeo estático               |
;| En la P1, el problema a continuación se caia en tiempo de ejecución.   |
;| Ahora veremos como debería expresarse para que el problema se detecte  |
;| en tiempo estático.                                                    |
;|========================================================================|


;funciones definidas + with + tipos correctos en la definición de funciones
;con respecto al tipo del cuerpo de las mismas, pero mantiene error en
;aplicacion de nand
(test (run '{
   {define {same {x : Num} {y : Num}} : Bool {= x y}}
   {define {nand {x : Any} {y : Any}} : Bool {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   } '() #t) #f)

;|========================================================================|
;| En el ejemplo anterior, todo sigue funcionando porque x e y se definen |
;| como Any en la definición de nand, por lo que tipea. Y como el if no   |
;| cae en ese caso, no genera error de ejecución.                         |
;|========================================================================|


;funciones definidas + with + tipos correctos en la definición de funciones
;con respecto al tipo del cuerpo de las mismas, manteniendo error en app
;de nand, pero indicando los tipos de x e y como Bool en la definición de nand,
;mas no en el with. Forzando a que caiga en la mala rama del if.
(test/exn (run '{
   {define {same {x : Num} {y : Num}} : Bool {= x y}}
   {define {nand {x : Bool} {y : Bool}} : Bool {! (&& x y)}}
   {with {{x 1} {y 2} {z #t} {w (nand #f #t)}}
         {if (! w) (same x y) (nand x y)}}
   } '() #t) "Runtime type error: expected Boolean found Number" )

;|========================================================================|
;| Se sigue cayendo en runtime mas no en static, porque no declaramos el  |
;| tipo de x e y en el with.                                              |
;|========================================================================|

;funciones definidas + with + tipos correctos en la definición de funciones
;con respecto al tipo del cuerpo de las mismas, manteniendo error en app
;de nand, pero indicando los tipos de x e y como Bool en la definición de nand,
;y también en el with
(test/exn (run '{
   {define {same {x : Num} {y : Num}} : Bool {= x y}}
   {define {nand {x : Bool} {y : Bool}} : Bool {! (&& x y)}}
   {with {{x : Num 1} {y : Num 2} {z #t} {w (nand #f #t)}}
         {if w (same x y) (nand x y)}}
   } '() #t) "Static type error: expected Bool found Num")

;|========================================================================|
;| Finalmente, el typechecker atrapó el error antes de la ejecución :)    |
;|========================================================================|