#lang play
(print-only-errors #t)
#| CC4101: Lenguajes de Programación
-- Tarea 1 Semestre Otoño 2021 (2021-1)
-- Alumno: Matías Vergara Silva
|#

#| ========= PARTE 1: LENGUAJE CON FUNCIONES DE PRIMER ORDEN |#


#| <fundef> ::= {define {<id> <id>*} <expr>}
-- define una funcion mediante n argumentos y una expresion (cuerpo
-- de la función)
|#
(deftype FunDef
  (fundef fname args body))

#|-----------------------------
Environment abstract data type: Env
empty-env  :: Env
extend-env :: Sym Val Env -> Env
env-lookup :: Sym Env -> Val (o error)

representation BNF:
<env> ::= (mtEnv)
        | (aEnv <id> <val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id val env))

(define empty-env  (mtEnv))
(define extend-env aEnv)
(define (env-lookup x env)
  (match env
    [(mtEnv) (error 'env-lookup "free identifier: ~a" x)]
    [(aEnv id val rest)
     (if (eq? id x)
         val
         (env-lookup x rest))]))

#| <expr> ::= <num>
         | <id> 
         | <bool>
         | {<unop> <expr>}                 operador unario: add1, sub1, !.
         | {<binop> <expr> <expr>}         operador binario: +, -, *, /, etc.
         | {if <expr> <expr> <expr>}       if (condition)(true)(false) 
         | {with {{<id> <expr>}*} <expr>}  
         | {<id> <expr>*}
-- representa una expresión en el lenguaje.
-- una expresión puede ser un número, un identificador, un booleano, un operador
-- (unario o binario), una sentencia condicional, una asignación o un identificador.
|#
(deftype Expr
  [id name]
  [bool b]
  [num n]
  [unop op param]
  [binop op l r]
  [if0 condition cond-true cond-false]
  [with idvals body]
  [fun args body]
  [app fid args])

#| in-list: Any List[any] -> boolean
-- retorna true si el el segundo parámetro está en la
-- lista entregada, false si no.
|#
(define (in-list value list)
 (cond
  [(empty? list) false]
  [(equal? (first list) value) true]
  [else (in-list value (rest list))]))

#| <unops> ::= ! | add1 | sub1
-- lista de operadores que toman un solo valor como parámetro.
|#
(define unops (list '! 'add1 'sub1))

#| <boolean-unops> ::= !
-- lista de operadores booleanos que toman un solo valor como parámetro.
|#
(define boolean-unops (list '!))

#| <is-boolean-unop>::= Procedure -> boolean
-- verifica si un operador dado opera sobre booleanos.
|#
(define (is-boolean-unop? x) (in-list x boolean-unops))

#| <is-binop>::= Procedure -> boolean
-- verifica si un operador dado está en la lista de unops.
|#
(define (is-unop? x) (in-list x unops))

#| <binops> ::= + | - | * | / | && | || / = | < | ...
-- lista de operadores que toman dos valores como parámetros.
|#
(define binops (list '+ '- '* '/ '&& '|| '> '< '>= '<=))

#| <boolean-binops> ::= || / &&
-- lista de operadores que toman dos valores como parámetros.
|#
(define parsed-boolean-binops (list '&& '!! '=))

#| <is-binop>::= Procedure -> boolean
-- verifica si un operador dado está en la lista de binops.
|#
(define (is-binop? x) (in-list x binops))

#| <is-boolean-binop>::= Procedure -> boolean
-- verifica si un operador dado opera sobre booleanos.
|#
(define (is-boolean-binop? x) (in-list x boolean-binops))

#| lookup-fundef: Id List[FunDef] -> FunDef o error
-- busca la funcion de nombre fname en la lista fundefs y la retorna
-- si es que la encuentra, o error en caso contrario
|#
(define (lookup-fundef fname fundefs)
  (match fundefs
    ['() (error "undefined function:" fname)]
    [(cons fd fds) (if (eq? (fundef-fname fd) fname)
                       fd
                       (lookup-fundef fname fds))]))



#| parse-binop: symbol -> procedure
-- realiza el match entre el simbolo de un operador
-- binario y el operador correspondiente
|#
(define (parse-binop bin)
  (match bin
    ['+ +]
    ['- -]
    ['* *]
    ['/ /]
    ['&& (lambda (x y) (and x y))]
    ['= =]
    ['|| (lambda (x y) (or x y))]
    ['> >]
    ['< <]
    ['>= >=]
    ['<= <=]))

#| parse-unop: symbol -> procedure
-- realiza el match entre el simbolo de un operador
-- unario y el operador correspondiente
|#
(define (parse-unop un)
  (match un
    ['! not]
    ['add1 add1]
    ['sub1 sub1]))


#| parse: Src -> Expr
-- convierte sintaxis concreta en sintaxis abstracta
|#
(define (parse src)
  (match src
    ['() '()] ; caso base para el with
    [(? number?) (num src)]
    [(? symbol?) (id src)]
    [(? boolean?) (bool src)]
    [(list (? is-binop? op) l r) (binop (parse-binop op) (parse l) (parse r))]
    [(list (? is-unop? op) param) (unop (parse-unop op) (parse param))]
    [(list 'if0 condition cond-true cond-false)
     (if0 (parse condition) (parse cond-true) (parse cond-false))]
    [(list 'with (? list? dict) body)
     (with (map (lambda(l) (list(car l) (parse (car(cdr l))))) dict)
           (parse body))]
    [(list (? symbol? fid) (? list? args)) (app fid (map parse args))]
    ))


; Error de runtime: booleano por numero
(define rtnumberboolean "Runtime type error: expected Number found Boolean")

;- expresaremos 'numero o booleano' como number|boolean.

#| interp-binop :: Expr x number|boolean x number|boolean -> number|boolean o error
-- verifica que los resultados de interpretar los operandos de un
-- operador binario correspondan a los tipos que dicho
-- operador puede operar, y en dicho caso, los opera.
|#
(define (interp-binop op l r)
  (if (and (number? l) (number? r))
      (op l r)
      (if (and (boolean? l) (boolean? r))
               (if (equal? op = )
                   (op l r)
                   (error rtnumberboolean)
                   )
               (error rtnumberboolean)
               )
      )
  )

#| interp-unop :: Expr x number|boolean -> number|boolean o error
-- verifica que lo resultados de interpretar los operandos de un
-- operador unario correspondan a los tipos que dicho operador puede operar
-- y en dicho caso, los opera.
|#
(define (interp-unop op param)
  (if (number? param)
      (op param)
      (if (is-boolean-unop? op)
          (op param)
          (error rtnumberboolean)
          )
      )
  )

#| interp :: Expr x List[FunDef] x Env -> number?
-- evalua una expresión aritmética
|#
(define (interp expr fundefs env)
  (match expr
    [(num n) n]
    [(id x) (env-lookup x env)]  ; buscamos el identificador en el env
    [(bool b) b]
    [(binop op l r)
     (interp-binop op (interp l fundefs env) (interp r fundefs env))]
    [(unop op arg)
     (interp-unop op (interp arg fundefs env))]
    [(if0 cond cond-true cond-false)
     (if (zero? (interp cond fundefs))
                (interp cond-true fundefs)
                (interp cond-false fundefs))]
    ))

   ; [(with dictlist b)
   ;  (interp b fundefs (extend-env x (interp e fundefs env) env))]

;    [(app f e)
 ;    (def (fundef _ arg body) (lookup-fundef f fundefs))
  ;   (interp body fundefs (extend-env arg (interp e fundefs env)
   ;                                   empty-env))])) ;; queremos scope lexico!
                                      ; si pasamos "env", tenemos scope dinamico



; run : Src x List[FunDef]? -> Val
(define (run prog [fundefs '()])
  (interp (parse prog) fundefs empty-env))
