#lang play
(print-only-errors #t)
(require "tarea1.rkt")
#| CC4101: Lenguajes de Programación
-- Tarea 1 Semestre Otoño 2021 (2021-1)
-- Alumno: Matías Vergara Silva
-- Script: tests pregunta 3: Contratos
|#

#| ======= TAREA 1: LENGUAJE CON FUNCIONES DE PRIMER ORDEN =======|#
#| -------  Tipos estáticos, tipos opcionales, contratos   -------|#
#| -----------------  Tests parte 3: Contratos   -----------------|#


#|------------------   Tests del enunciado  -----------------|#

(test (run '{{define {positive x} : Bool {> x 0}}
 {define {div {x : Num @ positive} y}
           {/ y x}}
 {div 5 3}} '() #t)
  3/5)

(test (run '{{define {positive x} : Bool {> x 0}}
 {define {div {x @ positive} y}  ; aquí sólo se especifica un contrato
           {/ y x}}
 {div 5 3}} '() #t)
  3/5)

(test (run '{
   {define {lt100 x} {< x 100}}
   {define {positive x} : Bool {> x 0}}
   {define {percentage? x} : Bool {&& {lt100 x} {positive x}}}
   {define {calc {x @ positive} {y @ percentage?}}
      {/ {* y y} x}}
   {calc 25 3}
} '() #t) 9/25)

           
(test/exn (run '{{define {positive x} : Any {> x 0}}
 {define {div {z : Num @ positive} y}
           {/ y -1}}
 {div -1 3}})
  "Static contract error: invalid type for positive")


#|------------------   Tests personalizados  -----------------|#
;multiples argumentos en funcion contrato
(test/exn (run '{{define {positive x y} : Bool {> x 0}}
 {define {div {z : Num @ positive} y}
           {/ y -1}}{div -1 3}} '() #t )
 "Static contract error: invalid type for positive")


;no cumplir con contrato
(test/exn (run '{{define {positive x} : Bool {> x 0}}
 {define {div {x : Num @ positive} y}
           {/ x y}}{div -1 3}} '() #f) 
  "Runtime contract error: -1 does not satisfy positive")

(test/exn (run '{{define {add x y} : Num {+ x y}}
         {define {oh-no {x @ add} y}
                    #t}
         {oh-no 21 21}})
          "Static contract error: invalid type for add")

;contratos que llaman a otros contratos - caso en que alguno no se cumple
(test/exn (run '{
   {define {lt100 x} {< x 100}}
   {define {positive x} : Bool {> x 0}}
   {define {percentage? x} : Bool {&& {lt100 x} {positive x}}}
   {define {calc {x @ positive} {y @ percentage?}}
      {/ {* y y} x}}
   {calc 25 -3}
} '() #t) "Runtime contract error: -3 does not satisfy percentage?")

;contratos que llaman a otros contratos - caso en que un contrato simple
;no es de tipo Bool
(test/exn (run '{
   {define {lt100 x} {< x 100}}
   {define {positive x} : Any {> x 0}}
   {define {percentage? x} : Bool {&& {lt100 x} {positive x}}}
   {define {calc {x @ positive} {y @ percentage?}}
      {/ {* y y} x}}
   {calc 25 -3}
} '() #t) "Static contract error: invalid type for positive")

;contratos que llaman a otros contratos - caso en que un contrato 
;definido en base a una función y otro contrato no es de tipo Bool
(test/exn (run '{
   {define {lt100 x} {< x 100}}
   {define {positive x} : Bool {> x 0}}
   {define {percentage? x} : Any {&& {lt100 x} {positive x}}}
   {define {calc {x @ positive} {y @ percentage?}}
      {/ {* y y} x}}
   {calc 25 -3}
} '() #t) "Static contract error: invalid type for percentage?")


;contratos con tipos definidos y errores que pasan a runtime gracias
; al comodin
(test/exn (run '{
   {define {lt100 {x : Any}} {< x 100}}
   {define {positive {x : Any}} : Bool {> x 0}}
   {define {percentage? {x : Any}} : Bool {&& {lt100 x} {positive x}}}
   {define {calc {x @ positive} {y @ percentage?}}
      {/ {* y y} x}}
   {calc #t -3}
} '() #t) "Runtime type error: expected Number found Boolean")

;contratos con expresion with
(test (run '{
   {define {lt100 {x : Num}} {with {{y : Num 100}} {< x y}}}
   {define {positive {x : Num}} : Bool {with {{w : Any 0}} {> x w}}}
   {define {percentage? {x : Num}} : Bool {&& {lt100 x} {positive x}}}
   {define {calc {x @ positive} {y @ percentage?}}
      {/ {* y y} x}}
   {calc 2 5}
} '() #t) 25/2)

;contratos con expresion if
;contrato percentagegt60 se cumple
(test (run '{
   {define {lt100 {x : Num}} {with {{y : Num 100}} {< x y}}}
   {define {gt60 {x : Num}} {with {{y : Num 60}} {> x y}}}
   {define {positive {x : Num}} : Bool {with {{w : Any 0}} {> x w}}}
   {define {percentagegt60? {x : Num}} : Bool {&& {if (&& (lt100 x) (gt60 x)) #t #f} {positive x}}}
   {define {calc {x @ positive} {y @ percentagegt60?}}
      {/ {* y y} x}}
   {calc 2 61}
} '() #t) 1860.5)

;contrato percentagegt60 no se cumple
(test/exn (run '{
   {define {lt100 {x : Num}} {with {{y : Num 100}} {< x y}}}
   {define {gt60 {x : Num}} {with {{y : Num 60}} {> x y}}}
   {define {positive {x : Num}} : Bool {with {{w : Any 0}} {> x w}}}
   {define {percentagegt60? {x : Num}} : Bool {&& {if (&& (lt100 x) (gt60 x)) #t #f} {positive x}}}
   {define {calc {x @ positive} {y @ percentagegt60?}}
      {/ {* y y} x}}
   {calc 2 60}
} '() #t) "Runtime contract error: 60 does not satisfy percentagegt60")