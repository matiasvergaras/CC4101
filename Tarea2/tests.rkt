#lang play

(require "main.rkt")
;; Test sub-module.
;; See http://blog.racket-lang.org/2012/06/submodules.html

;this tests should never fail; these are tests for MiniScheme+
(module+ test
  (test (run '{+ 1 1}) 2)

  (test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)

  (test (run '{< 1 2}) #t)

  (test (run '{local {{define x 1}}
                x}) 1)

  (test (run '{local {{define x 2}
                      {define y {local {{define x 1}} x}}}
                {+ x x}}) 4)

  ;; datatypes
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Empty}}}) #t)

  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)

  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Cons 1 2}}}) #t)

  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Cons 1 2}}}) #t)

  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Cons 1 2}}})
        #f)

  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)

  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Empty}}})
        #f)

  ;; match
  (test (run '{match 1 {case 1 => 2}}) 2)

  (test (run '{match 2
                {case 1 => 2}
                {case 2 => 3}})
        3)

  (test (run '{match #t {case #t => 2}}) 2)

  (test (run '{match #f
                {case #t => 2}
                {case #f => 3}})
        3)

  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n}
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}})
        #t)
  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n}
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}}) #t))

;tests for extended MiniScheme+
;uncomment sanity tests when you are ready
#;
(module+ sanity-tests
    (test (run '{local {{datatype Nat
                  {Zero}
                  {Succ n}}
                {define pred {fun {n}
                               {match n
                                 {case {Zero} => {Zero}}
                                 {case {Succ m} => m}}}}}
          {pred {Succ {Succ {Zero}}}}} "ppwu") "{Succ {Zero}}")

(test (run
 `{local ,stream-lib
          {local {,ones ,stream-take}
            {stream-take 11 ones}}} "pp") "{list 1 1 1 1 1 1 1 1 1 1 1}")

(test (run `{local ,stream-lib
          {local {,stream-zipWith ,fibs}
            {stream-take 10 fibs}}} "pp") "{list 1 1 2 3 5 8 13 21 34 55}")

(test (run `{local ,stream-lib
          {local {,ones ,stream-zipWith}
            {stream-take 10
                         {stream-zipWith
                          {fun {n m}
                               {+ n m}}
                          ones
                          ones}}}} "pp")  "{list 2 2 2 2 2 2 2 2 2 2}")
(test
(run `{local ,stream-lib
               {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
                 {stream-take 10 {merge-sort fibs fibs}}}} "pp")   "{list 1 1 1 1 2 2 3 3 5 5}"))

; TESTS PARA LAZY EVALUATION
; Altamente basados en lo discutido en el foro. 
(module+ lazy-tests

  ; Test del enunciado: argumento lazy, retorno de argumento normal.
  (test (run '{{fun {x  {lazy y}} x} 1 {/ 1 0}}) 1)

  ; Test del enunciado: argumentos normales, valor con division por 0.
  (test (run '{{fun {x  y} x} 1 {/ 1 0}}) "division by zero")

  ; Test del enunciado: argumento lazy mal formado que no se usa pues
  ; la evaluacion no requiere entrar a la variante.
  (test (run '{local {{datatype T 
                  {C {lazy a}}}
                {define x {C {/ 1 0}}}}
          {T? x}}) #t)

  ; Test del enunciado: argumento lazy mal formado que se usa en un
  ; match.
  (test (run '{local {{datatype T 
                  {C {lazy a}}}
                {define x {C {/ 1 0}}}}
          {match x
            {case {C a} => a}}}) "division by zero")

  ; Test del enunciado: argumento lazy bien formado que se usa en el
  ; cuerpo del programa que además es entregado mediante pretty-printing
  (test (run '{local {{datatype T {C a {lazy b}}}
                {define x {C  0 {+ 1 2}}}}
               x} "pp") "{C 0 3}")
  
  #| Este test comporta una división por 0 en un argumento lazy.
  -- Dado que el argumento es lazy, no se usa y no hay flag, no debería caer
  -- en un punto strict y por ende debería correr sin error, entregando
  -- un structV.
  |#
  (test (structV? (run '{local {{datatype T {C a {lazy b}}}
                                {define x {C  0 {/ 1 0}}}}
                          x})) #t)
  #| Este test comporta una división por 0 en un argumento lazy.
  -- Dado que el argumento es lazy, no se usa y no hay flag, no debería caer
  -- en un punto strict y por ende debería entregar, sin error, el resultado esperado.
  |#
  (test (run '{local {{datatype T 
                                {C {lazy a} b}}
                      {define x {C {/ 88 0} 2}}}
                {match x
                  {case {C z q} => q}}}) 2)

  #| Este test comporta una división por 0 en un argumento NO lazy.
  -- Dado que el argumento no es lazy, será evaluado (aun que no haya flag)
  -- y el programa deberá caerse con error de division por cero.
  |#
  (test/exn (run '{local {{datatype T 
                                    {C {lazy a} b}}
                          {define x {C 2 {/ 88 0}}}}
                    {match x
                      {case {C z {C r t}} => z}
                      {case {C h q} => h}}}) "division by zero")

  #| Mismo test anterior, pero ahora el valor no se usa.
  -- Aún en estas condiciones, dado que no se trata de un argumento lazy,
  -- deberá ser evaluado y el programa deberá caerse con error de division por cero.
  |#
  (test/exn (run '{local {{datatype T 
                                    {C {lazy a} b}}
                          {define x {C 2 {/ 88 0}}}}
                    {1}}) "division by zero")

  
  #| Este test comporta una división por 0 en un argumento NO lazy,
  -- el cual se usa para evaluar un pattern matching.
  -- En estas condiciones, el programa debe caerse con el error de div por 0,
  -- pues aún cuando el argumento no se usa, es necesario evaluarlo para reconocer el patrón.
  |#
  (test/exn (run '{local {{datatype T 
                                    {C {lazy a} {lazy b}}}
                          {define x {C 2 {/ 88 0}}}}
                    {match x
                      {case {C z {C r t}} => z}
                      {case {C h q} => h}}}) "division by zero")
  )

; TESTS PARA PRETTY-PRINTING 
(module+ simple-tests
  #| Tests simple para asegurar que el pretty-printing no interfiera con el retorno
  -- de valores que no correspondan a structV.
  |#
  (test (run '{+ 1 1} "ppwu") 2)
  (test (run '{(number? 1)}) #t)

 ; Test unitario del enunciado para pretty-printing 
 (test (pretty-printing (structV 'Nat 'Succ (list (structV 'Nat 'Zero empty))))
        "{Succ {Zero}}")
  
  ; Tests del enunciado para pretty-printing de structV desde run
  (test (run '{local {{datatype Nat 
                  {Zero} 
                  {Succ n}}
                {define twice {fun {n} 
                               {match n
                                 {case {Zero} => {Zero}}
                                 {case {Succ m} => {Succ {Succ {twice m}}}}}}}}
          {twice {Succ {Succ {Zero}}}}})
"{Succ {Succ {Succ {Succ {Zero}}}}}")

  ; Tests del enunciado para pretty-printing de list
  (test (run '{list 1 4 6} "pp") "{list 1 4 6}")
  ; Test del enunciado para pretty-printing de list vacia
  (test (run '{list} "pp") "{list}")
  )
