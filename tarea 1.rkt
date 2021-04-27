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
  (fundef fname arg body))

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
  [app fname args])

#| <unops> ::= ! | add1 | sub1
-- lista de operadores que toman un solo valor como parámetro.
|#
(define unops (list '! 'add1 'sub1))

#| <is-binop>::= Procedure -> boolean
-- verifica si un operador dado está en la lista de unops.
|#
(define (is-unop? x) (member x unops))

#| <binops> ::= + | - | * | / | && | = | < | ...
-- lista de operadores que toman dos valores como parámetros.
|#
(define binops (list '+ '- '* '/ '&& '|| '> '< '>= '<=))

#| <is-binop>::= Procedure -> boolean
-- verifica si un operador dado está en la lista de binops.
|#
(define (is-binop? x) (member x binops))


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
    ['(&&) (lambda (x y) (and x y))]
    ['= =]
    ['(||) (lambda (x y) (or x y))]
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
    [(? number?) (num src)]
    [(? symbol?) (id src)]
    [(? boolean?) (bool src)]
    [(list (? is-binop? op) l r) (binop (parse-binop op) (parse l) (parse r))]
    [(list (? is-unop? op) param) (unop (parse-unop op) (parse param))]
    [(list 'if condition cond-true cond-false) (if0 (parse condition) (parse true) (parse false))]
;--- para el caso del with, se itera recursivamente 'hacia adentro',
;--- y una vez que se tienen todos los with parseados, se parsea el body
    ['() '()] ; caso base 
    [( list 'with idvals body )
     (with (parse (list (car (car idvals)) (cdr(car idvals)) (cdr idvals))) parse(body))]
    [(list (? symbol? id) val (? pair? rest))
     (cons (cons id val) parse(list (car(car rest)) (car(cdr rest)) (cdr rest)))]
    ;[(list 'with named-exprs body)
     ; (with (parse (list (car(car named-exprs)) (cdr(car named-exprs)) (cdr named-exprs))) (parse body))]
    ;[(list (? symbol? id) val rest)
    ; (cons (with id val) (parse rest))]
;--- parser de funciones
    ;[(list 'fun (args(listof symbol?))
;--- parser de aplicaciones con posibilidad de multiples argumentos
    ;[(list (? symbol? fname) (args) )]
    ))


#|

; interp :: Expr x List[FunDef] x Env -> number?
; evalua una expresión aritmética
(define (interp expr fundefs env)
  (match expr
    [(num n) n]
    [(id x) (env-lookup x env)]  ; buscamos el identificador en el env
    [(add l r) (+ (interp l fundefs env) (interp r fundefs env))]
    [(sub l r) (- (interp l fundefs env) (interp r fundefs env))]
    [(with x e b)
     (interp b fundefs (extend-env x (interp e fundefs env) env))]
    [(app f e)
     (def (fundef _ arg body) (lookup-fundef f fundefs))
     (interp body fundefs (extend-env arg (interp e fundefs env)
                                      empty-env))])) ;; queremos scope lexico!
                                      ; si pasamos "env", tenemos scope dinamico


; run : Src x List[FunDef]? -> Val
(define (run prog [fundefs '()])
  (interp (parse prog) fundefs empty-env))

|#