#lang play
(print-only-errors #t)
#| CC4101: Lenguajes de Programación
-- Tarea 1 Semestre Otoño 2021 (2021-1)
-- Alumno: Matías Vergara Silva
|#

#| ========= PARTE 1: LENGUAJE CON FUNCIONES DE PRIMER ORDEN |#


#| <prog> ::= {<fundef>* <expr>}
-- un programa se compone de 0 o mas deifniciones de funciones y una expresion final
-- que sirve de punto de entrada.
|#
(deftype Prog
  (prog fundefs main))

  
#| <fundef> ::= {define {<id> <id>*} <expr>}
-- funciones de n argumentos y cuerpo
|#
(deftype FunDef
  (fundef fname args body))

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


#| <in-list>:: Any x List[Any] -> boolean
-- indica si el valor dado como primer parametro
-- esta presente en la lista dada como segundo
|#
(define (in-list v l)
  (cond
    [(equal? l empty) #f]
    [(equal? (first l) v) #true]
    [else (in-list v (cdr l))]))

#| <unops> ::= ! | add1 | sub1
-- lista de operadores que toman un solo valor como parámetro.
|#
(define unops (list '! 'add1 'sub1))
(define not-bool-unops(list 'add1 'sub1))

#| is-unop? ::= Procedure -> boolean
-- verifica si un operador dado está en la lista de unops.
|#
(define (is-unop? x) (member x unops))
(define (is-not-bool-unop? x) (in-list x not-bool-unops))

#| <binops> ::= + | - | * | / | && | || / = | < | ...
-- lista de operadores que toman dos valores como parámetros.
|#
(define binops (list '+ '- '* '/ '&& '|| '= '> '< '>= '<=))
(define not-bool-binops (list '+ '- '* '/ '> '< '>= '<=))

#| is-binop? ::= Procedure -> boolean
-- verifica si un operador dado está en la lista de binops.
|#
(define (is-binop? x) (member x binops))
(define (is-not-bool-binop? x) (in-list x not-bool-binops))

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
    ['= equal?]
    ['&& (lambda (x y) (and x y))]
    ['|| (lambda (x y) (or x y))]
    ['> >]
    ['>= >=]
    ['< <]
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
    [(list 'if condition cond-true cond-false)
     (if0 (parse condition) (parse cond-true) (parse cond-false))]
    [(list 'with (? list? dict) body)
     (with (map (lambda(entry) (list(car entry) (parse (car(cdr entry))))) dict)
           (parse body))]
    [(list 'define (? list? fname-args) body)
          ( fundef (first fname-args)
                   (map (lambda (entry) (parse entry)) (rest fname-args))
                   (parse body))]
    [(? list? args) 
     (cond
       [(symbol? (car args))(app (first args) (map parse (rest args)))] ; app
       [else (list (map (lambda (entry) ;prog
                  (cond
                    [(equal? (first entry) 'define) (parse entry)]
                        [else '()])) args)
           (parse (car (reverse args))))])]
    ))

(define a '{f {f 10 2}})
(listof 1)
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

; Error de runtime: booleano por numero
(define rtnumberboolean "Runtime type error: expected Number found Boolean")

#| interp :: Expr x List[FunDef] x Env -> number|boolean o error
-- evalua expresiones aritméticas y booleanas
|#
(define (interp expr fundefs env)
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
            (if (not (is-not-bool-binop? op))
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
        (if (not (is-not-bool-unop? op))
            (op param)
            (error rtnumberboolean)
            )
        )
    )
  #| extend-env-list :: List[Pair[symbol, expr]] x Env -> Env
  -- extiende el ambiente dado con los pares (identificador, expr)
  -- de la lista entregada como parametro, interpretando las expr.
  |#
  (define (extend-env-list dictlist)
    (cond
      [(empty? dictlist) env]
      [ else
        (extend-env (car (first dictlist))
                    (interp (car(cdr (first dictlist))) fundefs env)
                    (extend-env-list (rest dictlist)))]))

  #| app-map-list :: List[id] x List[expr] -> Env
  -- extiende el ambiente dado con los pares (identificador, expr)
  -- de la lista entregada como parametro, interpretando las expr.
  |#
  (define (app-map-list args es)
    (cond
      [(and (empty? args) (not empty? es)) (error "Not enough arguments")]
      [(and (not empty? args) (empty? es)) (error "Too many arguments")]
      [(and (empty? args) (empty? es)) empty-env]
      [else
        (extend-env ( first args )
                    ( interp (first es fundefs env) )
                    (app-map-list (rest args) (rest es)))]))
  
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
    [(with dictlist b)
     (interp b fundefs (extend-env-list dictlist))]
    [(app f es)
     (def (fundef _ args body) (lookup-fundef f fundefs))
     (interp body fundefs (app-map-list args es))] ;; queremos scope lexico!
    [(list aprog)
     (interp (car (rest aprog)) (car aprog)  empty-env)]
    ))



; run : Src x List[FunDef]? -> Val
(define (run prog [fundefs '()])
  (interp (parse prog) fundefs empty-env))
