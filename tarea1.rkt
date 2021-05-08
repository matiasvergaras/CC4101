#lang play
(print-only-errors #t)
#| CC4101: Lenguajes de Programación
-- Tarea 1 Semestre Otoño 2021 (2021-1)
-- Alumno: Matías Vergara Silva
|#

#| ========= PARTE 1: LENGUAJE CON FUNCIONES DE PRIMER ORDEN |#

#|
-- Definimos los errores como constantes para evitar escribirlos varias veces.
|#
; Error de runtime: booleano por numero
(define rtnumberboolean "Runtime type error: expected Number found Boolean")
; Error estatico: numero por booleano
(define stbooleannumber "Static type error: expected Bool found Num")
; Error estatico: booleano por numero
(define stnumberboolean "Static type error: expected Num found Bool")

#| <prog> ::= {<fundef>* <expr>}
-- un programa se compone de 0 o mas deifniciones de funciones y una expresion final
-- que sirve de punto de entrada.
|#
(deftype Prog
  (prog fundefs main))

  
#| <fundef> ::= {define {<id> <arg>*}[: <type>] <expr>}
-- funciones de n argumentos y cuerpo, con declaracion
-- opcional de tipos.
|#
(deftype FunDef
  (fundef fname args type body))

#| <arg> ::= <id> | {<id> : <type>}
-- representa un argumento de funcion:
-- un identificador y un tipo opcional.
|#
(deftype Arg
  (arg id type))

#| <type>:: = Num | Bool | Any
-- representa el tipo de una expresión, argumento o función.
|#
(deftype Type
  [Num]
  [Bool]
  [Any])

#|-----------------------------
Type environment abstract data type: Tenv
empty-Tenv  :: Tenv
extend-Tenv :: Sym Type Env -> Env
Tenv-lookup :: Sym Env -> Type (o error)

representation BNF:
<Tenv> ::= (mtTenv)
        | (aTenv <id> <Type> <env>)
|#

(deftype Tenv
  (mtTenv)
  (aTenv id t tenv))

(define empty-tenv  (mtTenv))
(define extend-tenv aTenv)

(define (tenv-lookup x tenv)
  (match tenv
    [(aTenv id t rest)
     (if (or (equal? id x) (equal? id (parse x)))
         t
         (tenv-lookup x rest))]
    [mtTenv (error (format "Static error: free identifier: ~a" x))]
    ))

#| extend-tenv-list :: List[Pair[arg, expr]] x Tenv -> Tenv
  -- extiende el ambiente de tipos dado con los args
  -- de la lista entregada como parametro.
  |#
(define (extend-tenv-list dictlist tenv)
  (cond
    [(empty? dictlist) tenv]
    [ else
      (extend-tenv (arg-id (car (first dictlist)))
                   (arg-type (car (first dictlist)))
                  (extend-tenv-list (rest dictlist) tenv))]))

#| parse-type: symbol -> Type
-- realiza el match entre la síntaxis abstracta de un tipo ('Num, 'Bool, 'Any)
-- y el tipo Type correspondiente.
|#
(define (parse-type src)
  (match src
    ['Num Num]
    ['Bool Bool]
    ['Any Any]
    [_ Any]
    ))

#| dsp-type: Type -> symbol
-- realiza el match inverso al de parse-type: de Type a sintaxis concreta
|#
(define (dsp-type t)
  (cond
    [(equal? Num t) 'Num]
    [(equal? Bool t) 'Bool]
    [else 'Any]))

#| string-type: Type -> string
-- entrega un string correspondiente al tipo ingresado.
-- Simplifica la sintaxis de los errores no triviales de mostrar
-- (aquellos en que T1 y T2 no son siempre el mismo).
|#
(define (string-type t)
  (cond
    [(equal? Num t) "Num"]
    [(equal? Bool t) "Bool"]
    [else "Any"]))

#| typecheck-unop: unop expr -> Type | error
-- recibe un operador unario y una expresion
-- y retorna el tipo del resultado de aplicar
-- el operador sobre la expresion,o error si cor
|#
(define (typecheck-unop op p tenv)
  (let([tp (typecheck-expr p tenv)])
  (cond
    [(equal? op not) (if (equal? tp Bool) Bool (error stbooleannumber))]
    [(equal? op add1) (if (equal? tp Num) Num (error stnumberboolean))]
    [(equal? op sub1) (if (equal? tp Num) Num (error stnumberboolean))]
    )))


#| typecheck-binop: binop expr expr -> Type | error
-- recibe un operador binario y dos expresiones
-- y retorna el tipo del resultado de aplicar
-- el operador sobre las expresiones, o error si coresponde
|#
(define (typecheck-binop op l r tenv)
  (define (bool-op-check t a b)
    (or (and (equal? a t) (equal? b t))
        (or (and (equal? a Any) (equal? b Any))
            (or (and (equal? a Any) (equal? b t))
                (or (and (equal? a t) (equal? b Any)))))))
  (define (get-predominant-type a b)
    (if (equal? a Any)
        a
        b))
  (let([tl (typecheck-expr l tenv)])
  (let([tr (typecheck-expr r tenv)])
  (cond
    [(equal? op equal?) (if (and (equal? tl Num)(equal? tr Num)) Num (error stnumberboolean))]
    [(equal? op +) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op -) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op /) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op *) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op =) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op >) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op <) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op <=) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [(equal? op >=) (if (bool-op-check Num tl tr) (get-predominant-type tl tr) (error stnumberboolean))]
    [else (if (bool-op-check Bool tl tr) (get-predominant-type tl tr) (error stbooleannumber))];lambdas && ||
    ))))        

#| check-pair: (cons arg expr) -> true | error
-- revisa si un par (argumento, valor) esta bien tipado.
-- retorna true en caso correcto, error en caso contrario.
|#
(define (typecheck-pair argval)
  (let([targ (arg-type (car argval))])
  (let([tval (typecheck-expr (car (cdr argval)) mtTenv)])
  (if  (or (equal? targ tval)
            (equal? targ Any))
         #t
         (error (string-append "Static type error. Expr type " (string-type tval)
                            " doesnt match Arg type "(string-type targ)))))))
  
#| typecheck-arg: list((arg, expr)) -> Bool | error
-- realiza el chequeo de tipos para una lista de pares (argumento, valor),
-- con valor en sintaxis abstracta (expr). 
-- si todos los valores calzan con el tipo declarado para el argumento,
-- retorna true. En caso contrario, false.
|#
(define (typecheck-arg argsvals)
  (let ([valid-list (map typecheck-pair argsvals)])
  (foldl (lambda (a b) (and a b)) #t argsvals)))

#| typecheck-expr: expr tenv -> Type | error
-- recibe una expresion, un ambiente de tipos
-- y retorna el tipo de la expresion
-- o error si es que corresp onde 
|#
(define (typecheck-expr expr tenv)
  (match expr
    [(id z) (tenv-lookup z tenv)] 
    [(num n) Num]
    [(bool b) Bool]
    [(unop op p)
     (typecheck-unop op p tenv)]
    [(binop op l r)
     (typecheck-binop op l r tenv)]
    [(if0 condition cond-true cond-false)
     (let([tcond (typecheck-expr condition tenv)])
     (let([ttrue (typecheck-expr cond-true tenv)])
     (let([tfalse (typecheck-expr cond-false tenv)])
     (if (equal? tcond Bool)
         (if (or (equal? ttrue tfalse) (or (equal? ttrue Any) (equal? tfalse Any)))
             (if (or (equal? ttrue Any) (equal? tfalse Any)) Any ttrue)
             (error (string-append "Static type error: found case-true: "(string-type ttrue) " case-false: "(string-type tfalse))))
         (error (string-append "Static type error: expected Bool found " (string-type tcond)))))))]
    [(with argsvals body)
     (if (typecheck-arg argsvals)
         (typecheck-expr body (extend-tenv-list argsvals tenv))
         (error "Static type error in with")) ; Debería haberse alertado antes.
     ]

   ))


#| typecheck-fun: Fundef -> Type | error
-- recibe una función y retorna su tipo
-- o error si es que corresponde 
|#
(define (typecheck-fun afun)
  (let([tfun (fundef-type afun)])
  (let([tbody (typecheck-expr (fundef-body afun) (extend-tenv-list (fundef-args afun) mtTenv))])
  (if (equal? tfun tbody)
      tfun
      (if (equal? tbody Any)
          tfun
          (error (string-append "Static type error. Function " (fundef-fname afun)
                                " declared type " (string-type tfun)
                                " but body has type " (string-type tbody))))))))


#| typecheck-prog: Prog -> Type | error
-- recibe un programa y retorna su tipo
-- o error si es que corresponde 
|#
(define (typecheck-prog aprog)
  (match aprog
    [(prog '() main)
     (displayln "program without functions")
     (typecheck-expr main mtTenv)
     ]
    [(prog fundefs main)
     (if (map typecheck-fun fundefs)
          (typecheck-expr main mtTenv)
          (error "There is a static error in fundefs, but typechecker was not able to
                   detect it :("))]
    ))

#| typecheck: expr -> Type | error
-- recibe la sintaxis concreta de un programa y retorna
-- la sintaxis concreta correspondiente al tipo del mismo,
-- o error si es que corresponde 
|#
(define (typecheck src)
  (dsp-type(typecheck-prog (parse-prog src)))
  )

  
#| <expr> ::= <num>
         | <id> 
         | <bool>
         | {<unop> <expr>}                 operador unario: add1, sub1, !.
         | {<binop> <expr> <expr>}         operador binario: +, -, *, /, etc.
         | {if <expr> <expr> <expr>}       if (condition)(true)(false) 
         | {with {{<id> <expr>}*} <expr>}  ; with P1, sin tipos
         | {with {{<arg> <expr>}*} <expr>} ; with P2 incorporacion de tipo
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
  [app fid args]
  )       

#| <in-list>:: a x List[any] -> boolean
-- indica si el valor dado como primer parametro
-- esta presente en la lista dada como segundo
|#
(define (in-list v l)
  (cond
    [(equal? l empty) #f]
    [(equal? (first l) v) #t]
    [else (in-list v (cdr l))]))

#| <unops> ::= ! | add1 | sub1
-- lista de operadores que toman un solo valor como parámetro.
|#
(define unops (list '! 'add1 'sub1))

#| not-bool-unop? ::= add1 | sub1
-- operadores unarios que no son booleanos
|#
(define not-bool-unops(list 'add1 'sub1))

#| is-unop? ::= Procedure -> boolean
-- verifica si un operador dado está en la lista de unops.
|#
(define (is-unop? x) (member x unops))

#| is-not-bool-unop? ::= symbol -> boolean
-- verifica si un operador dado en sintaxis concreta
-- no está en la lista de unops booleanos.
|#
(define (is-not-bool-unop? x) (in-list x not-bool-unops))

#| <binops> ::= + | - | * | / | && | || / = | < | ...
-- lista de operadores que toman dos valores como parámetros.
|#
(define binops (list '+ '- '* '/ '&& '|| '= '> '< '>= '<=))

#| not-bool-binops? ::= + | - | / | > | < | >= | <=
-- operadores binarios que no son booleanos
|#
(define not-bool-binops (list '+ '- '* '/ '> '< '>= '<= '=))

#| is-binop? ::= Procedure -> boolean
-- verifica si un operador dado está en la lista de binops.
|#
(define (is-binop? x) (member x binops))

#| is-not-bool-binop? ::= Symbol -> boolean
-- verifica si un operador dado en sintaxis concreta
-- no está en la lista de binops booleanos.
|#
(define (is-not-bool-binop? x) (in-list x not-bool-binops))

#| lookup-fundef: Id List[FunDef] -> FunDef o error
-- busca la funcion de nombre fname en la lista fundefs y la retorna
-- si es que la encuentra, o error en caso contrario
|#
(define (lookup-fundef fname fundefs)
  (match fundefs
    ['() (error "Static error: undefined function:" fname)]
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


#| parse-fun: Src -> Fundef
-- genera una funcion (en sintaxis abstracta) a partir del parseo del src.
|#
(define (parse-fun src)
  (match src
    [(list 'define (? list? fname-args) body)
     (fundef (first fname-args)
              (map (lambda (entry) (parse-arg entry)) (rest fname-args))
              Any (parse body))]
    
    [(list 'define (? list? fname-args) type body)
     (fundef (first fname-args)
             (map (lambda (entry) (parse-arg entry)) (rest fname-args))
             (parse-type type) (parse body))]
    ))



#| parse-prog: Src -> Prog
-- genera un programa (sintaxis abstracta) a partir del parseo del src.
-- Primero parsea las funciones, luego llama al parser habitual
-- para generar una expr con el candidato a main.
|#
(define (parse-prog src)
  (match src
     [(list body)
       (prog empty (parse body))]
     [(list fundefs ... main)
      (prog (map (lambda (entry) (parse-fun entry)) fundefs) (parse main))]))

#| interp-prog: Prog -> number|boolean|error
-- interpreta un programa, recuperando las definiciones de funciones
-- y el main, para entregarlos como argumentos al interprete de
-- expresiones (expr).
|#
(define (interp-prog program fundefs env)
  (interp (prog-main program) (append (prog-fundefs program) fundefs) empty-env))


#| parse: Src -> Expr
-- convierte sintaxis concreta en sintaxis abstracta
|#
(define (parse src)
  (match src
    ['() '()] ; caso base para el with
    [(? number?) (num src)]
    [(? symbol?) (id src)]
    [(? boolean?) (bool src)]
    [(list (? is-binop? op) l r)
     (binop (parse-binop op) (parse l) (parse r))]
    [(list (? is-unop? op) param)
     (unop (parse-unop op) (parse param))]
    [(list 'if condition cond-true cond-false)
     (if0 (parse condition) (parse cond-true) (parse cond-false))]
    [(list 'with (? list? dict) body)
     (with (map (lambda(entry) (list (parse-arg entry) (parse (car(reverse entry))))) dict)
           (parse body))]
    [(? list? args) 
     (app (first args) (map parse (rest args)))] ;app
    ))

#| parse-arg: Src -> Arg
-- convierte sintaxis concreta en sintaxis abstracta
-- del tipo argumento (arg)
|#
(define (parse-arg src)
  (match src
  [(list x val)               ; caso with ... { id val} ... y define f { id } 
   (arg x Any)]
  [(list x ': t val)          ; caso with ... { id : type val } ...
   (arg x (parse-type t))]
  [(list x ': t)              ; caso define f { id : type }
   (arg x (parse-type t))]
  ))

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
     (if (or (equal? id x) (equal? id (parse x)))
         val
         (env-lookup x rest))]))



#| interp :: Expr x List[FunDef] x Env -> number|boolean o error
-- evalua expresiones aritméticas y booleanas
|#
(define (interp expr fundefs env)
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
  (define (extend-env-list dictlist env)
    (cond
      [(empty? dictlist) env]
      [ else
        (extend-env (car (first dictlist))
                    (interp (car(cdr (first dictlist))) fundefs env)
                    (extend-env-list (rest dictlist) env))]))

  #| app-map-list :: List[id] x List[expr] -> Env
  -- extiende el ambiente dado con los pares (identificador, expr)
  -- de la lista entregada como parametro, interpretando las expr.
  |#
  (define (app-map-list args es)
    (cond
      [(and (empty? args) (not (empty? es))) (error "Not enough arguments")]
      [(and (not (empty? args)) (empty? es)) (error "Too many arguments")]
      [(and (empty? args) (empty? es)) empty-env]
      [else
        (extend-env ( first args )
                    ( interp (first es) fundefs env )
                    (app-map-list (rest args) (rest es)))]))
  
  (match expr
    [(num n) n]
    [(id x) (env-lookup x env)]  ; buscamos el identificador en el env
    [(bool b) b]
    [(binop op l r)
     (interp-binop op (interp l fundefs env) (interp r fundefs env))]
    [(unop op arg)
     (interp-unop op (interp arg fundefs env))]
    [(if0 condition cond-true cond-false)
     (if (interp condition fundefs env)
                (interp cond-true fundefs env)
                (interp cond-false fundefs env))]
    [(with dictlist b)
     (interp b fundefs (extend-env-list dictlist env))]
    [(app f es)
     (def (fundef _ args type body) (lookup-fundef f fundefs))
     (interp body fundefs (app-map-list args es))] ;; queremos scope lexico!
    ))



; run : Src x List[FunDef]? -> Val
(define (run prog [fundefs '()])
  (define parsed-prog (parse-prog prog))
    (if (typecheck-prog parsed-prog empty-tenv)
        (interp-prog parsed-prog fundefs empty-env)
        (error "Typecheck failed, but it didnt report any specific error :(")))

