#lang play
(print-only-errors #t)
#| CC4101: Lenguajes de Programación
-- Tarea 2 Semestre Otoño 2021 (2021-1)
-- Alumno: Matías Vergara Silva
-- Script principal
|#

#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}
         | {match <expr> <case>+}

<case> ::= {'case <pattern> '=> <expr>}
<pattern> ::= <num>
         | <bool>
         | <string>
         | <id>
         | (<constr-id> <attr-id>*)

<def>  ::= {define <id> <expr>}
         | {datatype <typename> <type-constructor>*}}


<type-constructor> ::= {<id> <member>*}
<constr-id> :: = <id>
<attr-id> :: = <id>
<typename> :: = <id>
<member>   :: = <id>

|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim-app name args)   ; aplicación de primitivas
  (fun id body)
  (lcal defs body)
  (mtch val cases))

; definiciones
(deftype Def
  (dfine name val-expr) ; define
  (datatype name variants)) ; datatype

; variantes                   #un datatype tiene un nombre y distintas variantes
(deftype Variant
  (variant name params))

; estructuras de datos        #una estructura de datos tiene un nombre, una variante y valores
(deftype Struct              
  (structV name variant values))

; caso en pattern matching
(deftype Case
  (cse pattern body))

; patrón
(deftype Pattern
  (idP id) ; identificador
  (litP l) ; valor literal
  (constrP ctr patterns)) ; constructor y sub-patrones


; lazy
(deftype LazyF
  (numV n)
  (closureF f arg-ids)         ; funciones
  (exprF expr env cache)) ; argumentos

#| parse :: s-expr -> Expr
-- toma sintaxis concreta y retorna una Expr (sintaxis abstracta).
-- se modifica version entregada para agregar parseo del tipo
-- inductivo List, incorporando '{list ...} como azucar sintáctico.
|#
(define (parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(? symbol?) (id s-expr)]
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'with (list (list x e) ...) b)
     (app (fun x (parse b)) (map parse e))]
    [(list 'list) ; inductive type List , case Empty 
     (parse (list 'Empty))] 
    [(list 'list vals ...) ; inductive type List, case Cons 
     (parse (list 'Cons (first vals) (list* 'list (rest vals))))] ;* to catch the final '()
    [(list 'local defs body)                                      ;as tail of the last element
     (lcal (map parse-def defs) (parse body))]
    [(list 'match val-expr cases ...) ; note the elipsis to match n elements
     (mtch (parse val-expr) (map parse-case cases))] ; cases is a list
    [(list f args ...) ; same here
     (if (assq f *primitives*)
         (prim-app f (map parse args)) ; args is a list
         (app (parse f) (map parse args)))]
  ))

; parse-def :: s-expr -> Def
(define(parse-def s-expr)
  (match s-expr
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'datatype name variants ...) (datatype name (map parse-variant variants))]))

; parse-variant :: sexpr -> Variant
(define(parse-variant v)
  (match v
    [(list name params ...) (variant name params)]))

; parse-case :: sexpr -> Case
(define(parse-case c)
  (match c
    [(list 'case pattern => body) (cse (parse-pattern pattern) (parse body))]))

; parse-pattern :: sexpr -> Pattern
(define (parse-pattern p)
  (match p
    [(? symbol?)  (idP p)]
    [(? number?)  (litP (num p))]
    [(? boolean?) (litP (bool p))]
    [(? string?)  (litP (str p))]
    ;same parsing for List as defined in parse
    [(list 'list) ; inductive type List , case Empty 
     (parse-pattern (list 'Empty))] 
    [(list 'list vals ...) ; inductive type List, case Cons 
     (parse-pattern (list 'Cons (first vals) (list* 'list (rest vals))))]
    [(list ctr patterns ...) (constrP (first p) (map parse-pattern patterns))]
    ))

#| strict :: closureF/number/boolean/procedure/struct
--        -> error/number/boolean/procedure/struct
-- Recibe un valor producto de interp, y en caso de que este sea una
-- promesa de evaluación, lo evalúa, entregando el valor correspondiente.
; evalua los puntos de strictness. En caso de encontrar una promesa (ExprV)
|#
(define (strict val)
  (match val
    [(exprF expr env cache)
     (if (not (equal? (unbox cache) "undefined"))
         (unbox cache)
         (let ([inval (strict (interp expr env))])
           (set-box! cache inval)
           inval))]
    [_ val]))

;; interp :: Expr Env -> number/boolean/procedure/Struct
(define (interp expr env)
#| get-id :: list(symbol)/symbol ->symbol
-- recibe un id o bien una lista '(lazy id).
-- Retorna el id directamente, sin lista ni lazy. 
|#
  (define (get-id id)
    (if (symbol? id) id (first (reverse id)))) 
  (match expr
    ; literals
    [(num n) n]
    [(bool b) b]
    [(str s) s]
    ; conditional
    [(ifc c t f)
     (if (interp c env)
         (interp t env)
         (interp f env))]
    ; identifier
    [(id x) (strict (env-lookup x env))]
    ; function (notice the meta interpretation)
    ; ya que las cosas lazy pueden ser o argumentos o constructores de funciones,
    ; debemos modificar el interprete de fun y de app. 
    [(fun ids body)
     (closureF (λ (arg-vals)(interp body (extend-env (map get-id ids) arg-vals env))) ids)]
    ; application
     [(app fun-expr arg-expr-list)
     (match (interp fun-expr env)
       [(closureF f arg-id-list)
        (f (map (lambda (exp id) ;lambda desempacando de dos listas: expr e id
                (match id
                  [(list 'lazy x) (exprF exp env (box "undefined"))];promesa de ev. de arg
                  [else (interp exp env)]));arg de evaluación inmediata
             arg-expr-list arg-id-list))]
       [(? procedure? p) (p (map (lambda (a) (interp a env)) arg-expr-list))])]
    [(app fun-expr arg-expr-list)
     ((interp fun-expr env)
      (map (λ (a) (interp a env)) arg-expr-list))]
    ; primitive application
    [(prim-app prim arg-expr-list)
     (apply (cadr (assq prim *primitives*))
            (map (λ (a) (interp a env)) arg-expr-list))]
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))
     (for-each (λ (d) (interp-def d new-env)) defs)
     (interp body new-env)]
    ; pattern matching
    [(mtch expr cases)
     (def value-matched (interp expr env))
     (def (cons alist body) (find-first-matching-case value-matched cases))
     (interp body (extend-env (map car alist) (map cdr alist) env))]))

; interp-def :: Def Env -> Void
(define (interp-def d env)
  (match d
    [(dfine id val-expr)
     (update-env! id (interp val-expr env) env)]
    [(datatype name variants)
     ;; extend environment with new definitions corresponding to the datatype
     (interp-datatype name env)
     (for-each (λ (v) (interp-variant name v env)) variants)]))

; interp-datatype :: String Env -> Void
(define (interp-datatype name env)
  ; datatype predicate, eg. Nat?
  (update-env! (string->symbol (string-append (symbol->string name) "?"))
               (λ (v) (symbol=? (structV-name (first v)) name))
               env))

; interp-variant :: String String Env -> Void
(define (interp-variant name var env)
  ;; name of the variant or dataconstructor
  (def varname (variant-name var))
  ;; variant data constructor, eg. Zero, Succ
  (update-env! varname
          (closureF (λ (args) (structV name varname args)) (variant-params var)) env)
  ;; variant predicate, eg. Zero?, Succ?
  (update-env! (string->symbol (string-append (symbol->string varname) "?"))
               (λ (v) (symbol=? (structV-variant (first v)) varname))
               env))

;;;;; pattern matcher
(define (find-first-matching-case value cases)
  (match cases
    [(list) #f]
    [(cons (cse pattern body) cs)
     (let [(r (match-pattern-with-value pattern value))]
       (if (foldl (λ (x y)(and x y)) #t r)
           (cons r body)
           (find-first-matching-case value cs)))]))

(define (match-pattern-with-value pattern value)
  (match/values (values pattern value)
                [((idP i) v) (list (cons i v))]
                [((litP (bool v)) b)
                 (if (equal? v b) (list) (list #f))]
                [((litP (num v)) n)
                 (if (equal? v n) (list) (list #f))]
                [((constrP ctr patterns) (structV _ ctr-name str-values))
                 (if (symbol=? ctr ctr-name)
                     (apply append (map match-pattern-with-value
                                        patterns str-values))
                     (list #f))]
                [(x y) (error "Match failure")]))


#| run :: s-expr [String] -> number/boolean/procedura/struct/String 
-- recibe una s-expr y, opcionalmente, un flag indicando si usar
-- pretty-printing: "ppwu". Retorna el resultado de parsear e interpretar la s-expr
-- en un ambiente con la estructura de datos 'List' y la función 'length'.
|#
(define (run prog [flag ""])
  (let [(res (interp (parse (list 'local my-list prog)) empty-env))]
    (match res
      [(structV name variant values)
       (match flag
         ["" res]
         ["ppwu" (pretty-printing (structV name variant (map strict values)) flag)]
         ["pp" (pretty-printing (structV name variant (map strict values)) flag)]
         )]
      [_ res])
    )
  )
  

#|-----------------------------
Environment abstract data type
empty-env   :: Env
env-lookup  :: Sym Env -> Val
extend-env  :: List[Sym] List[Val] Env -> Env
update-env! :: Sym Val Env -> Void
|#
(deftype Env
  (mtEnv)
  (aEnv bindings rest)) ; bindings is a list of pairs (id . val)

(def empty-env  (mtEnv))

(define (env-lookup id env)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" id)]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
     (if binding
         (cdr binding)
         (env-lookup id rest))]))

(define (extend-env ids vals env)
  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))

;; imperative update of env, adding/overriding the binding for id.
(define (update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+       ,(lambda args (apply + args)))
    (-       ,(lambda args (apply - args)))
    (*       ,(lambda args (apply * args)))
    (%       ,(lambda args (apply modulo args)))
    (odd?    ,(lambda args (apply odd? args)))
    (even?   ,(lambda args (apply even? args)))
    (/       ,(lambda args (apply / args)))
    (=       ,(lambda args (apply = args)))
    (<       ,(lambda args (apply < args)))
    (<=      ,(lambda args (apply <= args)))
    (>       ,(lambda args (apply > args)))
    (>=      ,(lambda args (apply >= args)))
    (zero?   ,(lambda args (apply zero? args)))
    (not     ,(lambda args (apply not args)))
    (and     ,(lambda args (apply (lambda (x y) (and x y)) args)))
    (or      ,(lambda args (apply (lambda (x y) (or x y)) args)))))


  
#| pretty-printing :: <structV> -> String
-- recibe un structV y lo retorna como un string mas amigable al usuario
|#
(define (pretty-printing intp [flag ""])
  (match intp
    [(structV 'List variant values) ;most specific case: structV name is 'List
     (if (equal? flag "pp")
         (string-append "{list" (List-to-string intp) "}") ;pp
         (string-append "{" (symbol->string variant) (pp-assigner values flag) "}") ;ppwu
         )]
    [(structV name variant values) ;general case, use ppwu
     (string-append "{" (symbol->string variant) (pp-assigner values flag) "}")]
    ))

#|
-- pp-assigner: structV/list/number/boolean -> string
-- Recibe un valor desde interp y lo retorna como string.
-- Realiza la asignación al pretty-printer correspondiente para el tipo de datos
-- recibido. Se implementa para evitar duplicar código en cada llamado
|#
(define (pp-assigner intp flag)
  (match intp
    [(? structV? intp) (pretty-printing intp flag)]
    [(? list? intp) (pretty-printing-list intp flag)]
    [(? number? intp) (pretty-printing-val intp)]
    [(? boolean? intp) (pretty-printing-val intp)])
  )

#|
-- pretty-printing-list: list -> string
-- función auxiliar para mantener pretty-printing recibiendo unicamente estructuras.
-- recibe una lista y la retorna como string usando el azucar sintactica "{list a b c ...}"
|#
(define (pretty-printing-list intp flag)
  (match intp
    [(list vals ...)
     (foldr (lambda (a b) (string-append " " (pp-assigner a flag) b)) "" vals)]
    
    )
  )

#|
-- pretty-printing-val: number/boolean -> string
-- función auxiliar para mantener pretty-printing-list recibiendo unicamente listas.
-- recibe valores numericos o booleanos y los retorna como string.
|#
(define (pretty-printing-val intp)
  (match intp
    [(? number? n) (number->string n)]
    [(? boolean? b) b]))

#| List-to-string :: <structV 'List variant values> -> String
-- recibe una structV cuyo nombre es List. Retorna los valores de la lista 
-- en formato "v1 v2 v3". 
|# 
(define (List-to-string aList)
  (match aList
    [(structV 'List 'Empty _) ""]
    [(structV 'List 'Cons values)
     (string-append " " (~a (first values)) (List-to-string (first (rest values))))]
    ))



#| my-list :: Void -> List
-- retorna una lista de Racket con la sintaxis concreta de un 
-- datatype List, con los constructores Empty y Cons, además
-- de la definición recursiva de length (largo de una lista). 
|#
(define my-list
  '{{datatype List
     {Empty}
     {Cons a b}}
   {define length
     {fun (first-element)
          {match first-element
            {case {Empty} => 0}
            {case {Cons a b} => {+ 1 {length b}}}}}}})


#| stream-data :: None -> Stream
-- Define una estructura de tipo Stream,
-- la cual no evalua su cola a menos que sea estrictamente necesario.
-- Stream :: {datatype stream <first> <rest>*}}
|#
(def stream-data '{datatype Stream {stream hd {lazy tl}}})

#| make-stream :: value x value -> Stream
-- Recibe dos valores y construye un stream basado en la estructura de
-- stream-data, poniendo como primer valor del stream el primer valor recibido
-- y como cola (lazy) el segundo.
|#
(def make-stream '{define make-stream {fun {hd {lazy tl}} {stream hd tl}}})

#| ones :: None -> (Stream 1 1 1 ...)
-- Crea un stream de 1's (una lista infinita que se evalua bajo necesidad).
|#
(def ones '{define ones {make-stream 1 ones}})

#| stream-hd: <Stream> -> value
-- recibe un stream y retorna su primer valor, tal cual 'head' para listas.
|#
(def stream-hd
  '{define stream-hd {fun {x}
                          {match x
                            {case {stream hd tl} => hd}}}})

#| stream-tl: <Stream> -> <Stream>
-- recibe un stream y retorna su cola, que es otro stream.
-- comportamiento analogo a 'rest' para listas.
|#
(def stream-tl
  '{define stream-tl {fun {x}
                          {match x
                            {case {stream hd tl} => tl}}}})


#| stream-take: Integer x <Stream> -> <List a b c ...>
-- recibe un entero n y un stream. Retorna los primeros n valores del stream.
|#
(def stream-take
  '{define stream-take {fun {n aStream}
                            {if {> n 0}
                                {Cons {stream-hd aStream} {stream-take {- n 1} {stream-tl aStream}}}
                                {Empty}}
                            }})
#| stream-lib: None -> List 
-- librería del enunciado, necesaria para inicializar lo relacionado a streams
-- sin necesidad de volver a definir las funciones en cada programa.
-- se entrega como definición local en los programas.
|#
(def stream-lib (list stream-data
                      make-stream
                      stream-hd
                      stream-tl
                      stream-take))

#| stream-zipWith: <fun><Stream><Stream> -> <Stream> 
-- combina dos streams mediante la aplicación de una función que recibe dos elementos 
-- de forma pair-wise: el n-esimo elem. del primer stream se combina con el n-esimo del segundo stream.
-- El resultado es otro stream.
|#
(def stream-zipWith
  '{define stream-zipWith {fun {combineFun stream1 stream2}
                               {make-stream {combineFun {stream-hd stream1} {stream-hd stream2}}
                                            {stream-zipWith
                                             combineFun {stream-tl stream1}
                                             {stream-tl stream2}}}
                               }})
#| fibs: None --> <Stream>
-- No recibe ningún parámetro y entrega el stream de los números de Fibonacci.
|#
(def fibs
  '{define fibs {make-stream 1 {make-stream 1 {stream-zipWith {fun {prev1 prev2} {+ prev1 prev2}}
                                                              fibs {stream-tl fibs}}}}})

#| merge-sort: 
-- Recibe dos streams, que deben venir ordenados.
-- retorna un stream con la mezcla de ambos, ordenada. 
|#
(def merge-sort
  '{define merge-sort {fun {s1 s2}
                           {if {< {stream-hd s1} {stream-hd s2}}
                               {make-stream {stream-hd s1} {merge-sort {stream-tl s1} s2}} 
                               {make-stream {stream-hd s2} {merge-sort s1 {stream-tl s2}}} 
                               }
                           }})
