#lang play

#|
<expr> ::= <num>
         | <id>
         | <bool>
         | (if <expr> <expr> <expr>)
         | (+ <expr> <expr>)
         | '< <s-expr> <s-expr>)
         | (* <s-expr> <s-expr>)
         | (= <s-expr> <s-expr>)
         | (- <s-expr> <s-expr>)
         | (and <s-expr> <s-expr>)
         | (or <s-expr> <s-expr>)
         | (not <s-expr> <s-expr>)
         | (seqn <expr> <expr>)
         | (local { <def> ...} <expr>)

<def>    ::= (define <id> <expr>)


;EXTENSION PARA OBJETOS
<expr>  ::= ... (todo lo anterior)
         | (object [: <expr>] <member> ...)
         | this
         | (set <id> <expr>)
         | (get <id>)
         | (send <expr> <id> <expr> ...)
         | (shallow-copy <expr>)
         | (deep-copy <expr>)
|#

(deftype Expr
  (num n)
  (bool b)
  (id s)
  (binop f l r)
  (unop f s)
  (my-if c tb fb)
  (seqn expr1 expr2)
  (lcal defs body)
  (object dlg members)
  (get fld-id)
  (set fld-id e)
  (send obj met-id vals)
  (this)
  (shallow-copy obj)
  (deep-copy obj)
  )

#| <member> ::=
        | (field <id> <s-expr>)
        | (method <id> (list <id> ...) <s-expr>)
|#
(deftype Member
  (field fld-id e)
  (method met-id args e))


;; values
(deftype Val
  (numV n)
  (boolV b)
  (objV fields methods objectEnv delegateEnv) ;;objetos como valores del lenguaje con
                                              ;;campos, metodos, ambiente de definición
                                              ;;y ambiente de delegación.
  )

(deftype Def
  (my-def id expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Environment abstract data type

empty-env        :: Env
env-lookup       :: Sym Env -> Val
multi-extend-env :: List<Sym> List<Val> Env -> Env
extend-frame-env! :: Sym Val Env -> Env


representation BNF:
<env> ::= (mtEnv)
        | (aEnv <id> <val> <env>)
|#

(deftype Env
  (mtEnv)
  (aEnv hash env))

(def empty-env (mtEnv))

#|
env-lookup:: Sym Env -> Val
Busca un símbolo en el ambiente, retornando su valor asociado.
|#
(define (env-lookup x env)
  (match env
    [(mtEnv) (error 'env-lookup "free identifier: ~a" x)]
    [(aEnv hash rest) (hash-ref hash x (λ () (env-lookup x rest)))]))

#|
multi-extend-env:: List(Sym) List(Expr) Env -> Env
Crea un nuevo ambiente asociando los símbolos a sus valores.
|#
(define (multi-extend-env ids exprs env)
  (if (= (length ids) (length exprs))
      (aEnv (make-immutable-hash (map cons ids exprs)) env)
      (error "wrong_input, mismatched lengths")))

#|
extend-frame-env!:: Sym Val Env -> Void
Agrega un nuevo par (Sym, Val) al ambiente usando mutación.
Este método no crea un nuevo ambiente.
|#
(define (extend-frame-env! id val env)
  (match env
    [(mtEnv) (aEnv (hash id val) env)]
    [(aEnv h rEnv) (def hupd (hash-set h id val))
                   (set-aEnv-hash! env hupd)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Member environment abstract data type
We will use a member env to represent both a field and a method list

empty-memberEnv            :: MemberEnv
lookup-memberEnv           :: Sym MemberEnv -> Val
extend-memberEnv           :: Sym Val|Expr MemberEnv -> MemberEnv


representation BNF:
<memberEnv> ::= (mtMemberEnv)
        | (aMemberEnv <id> <val> <memberEnv>)
|#

(deftype MemberEnv
  (mtMemberEnv)
  (aMemberEnv id val memberEnv))

#|
empty-memberEnv:: None -> memberEnv
representa un ambiente de miembros vacío.
|#
(define empty-memberEnv  (mtMemberEnv))

#|
extend-memberEnv:: id val|expr memberEnv -> memberEnv
crea un ambiente de miembros a partir de otro agregando
una nueva asociación id, valor. 
|#
(define extend-memberEnv aMemberEnv)

#|
lookup-memberEnv:: id 
|#
(define (lookup-memberEnv x memberEnv)
  (match memberEnv
    [(mtMemberEnv) 'undefined]
    [(aMemberEnv id memval rest)
     (if (eq? id x)
         memval
         (lookup-memberEnv x rest))]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; parse :: s-expr -> Expr
(define (parse s-expr)
  (match s-expr
    ['this (this)]
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [(? boolean?) (bool s-expr)]
    [(list '* l r) (binop * (parse l) (parse r))]
    [(list '+ l r) (binop + (parse l) (parse r))]
    [(list '- l r) (binop - (parse l) (parse r))]
    [(list '< l r) (binop < (parse l) (parse r))]
    [(list '= l r) (binop = (parse l) (parse r))]
    [(list 'or l r) (binop (λ (i d) (or i d)) (parse l) (parse r))]
    [(list 'and l r) (binop (λ (i d) (and i d)) (parse l) (parse r))]
    [(list 'not b) (unop not (parse b))]
    [(list 'if c t f) (my-if (parse c)
                             (parse t)
                             (parse f))]
    [(list 'seqn e1 e2) (seqn (parse e1) (parse e2))]
    [(list 'local (list e ...)  b)
     (lcal (map parse-def e) (parse b))]
    [(list 'object ': delegation members ...) (object (parse delegation) (map parse-member members))] ; objetos con delegación
    [(list 'object  members ...) (object null (map parse-member members))] ; objetos sin delegación
    [(list 'get fld-id) (get fld-id)] 
    [(list 'set fld-id e) (set fld-id (parse e))] 
    [(list 'send obj met-id vals ...)(send (parse obj) met-id (map parse vals))]
    [(list 'shallow-copy obj) (shallow-copy (parse obj))]
    [(list 'deep-copy obj) (deep-copy (parse obj))]
    [(list 'fun (list vals ...) body)(object null (list (method (id 'fun) vals (parse body))))]
    [(list fun app ...) (send (parse fun) (id 'fun) (map parse app))]))

;; parse-member :: s-expr -> Member
;; Recibe una s-expr correspondiente a un member (field o method)
;; y retorna el parseo de la misma (sintaxis abstracta).
(define (parse-member s-expr)
  (match s-expr
    [(list 'field fld-id e) (field fld-id (parse e))]
    [(list 'method meth-id (list vals ...) e) (method meth-id vals (parse e))]))

;; parse-def :: s-expr -> Def
(define (parse-def s-expr)
  (match s-expr
    [(list 'define id b) (my-def id (parse b))]))


;; interp :: Expr Env [objV|null] [objV|null] -> Val
;; Se agregan dos parametros opcionales:
;; uno para indicar el objeto dentro del cual se está interpretando (para el get, set y this)
;; y otro para indicar el objeto que llama (para el this).
(define (interp expr env [obj null] [caller null])
  (match expr
    [(num n) (numV n)]
    [(bool b) (boolV b)]
    [(binop f l r) (make-val (f (open-val (interp l env obj caller))
                                (open-val (interp r env obj caller))))]
    [(unop f s) (make-val (f (open-val (interp s env obj caller))))]
    [(my-if c t f)
     (def (boolV cnd) (interp c env obj caller))
     (if cnd
         (interp t env obj caller)
         (interp f env obj caller))]
    [(id x) (env-lookup x env)]
    [(seqn expr1 expr2) (begin
                          (interp expr1 env obj caller)
                          (interp expr2 env obj caller))]
    [(lcal defs body)
     (let ([new-env (multi-extend-env '() '() env)])
       (for-each (λ(x)
                   (def (cons id val) (interp-def x new-env))
                   (extend-frame-env! id val  new-env)
                   #t) defs)
       (interp body new-env obj caller))
     ]
    ;object
    [(object del members)
     (def methods_box (box empty-memberEnv))
     (def fields_box (box empty-memberEnv))
     (map (lambda (m) (match m
                        [(field fld-id fld-ex)
                         (set-box! fields_box (extend-memberEnv
                                               fld-id (interp fld-ex env obj caller) (unbox fields_box)))]
                        [(method met-id met-args met-exp)
                         (set-box! methods_box (extend-memberEnv
                                                met-id (cons met-args met-exp) (unbox methods_box)))])
            ) members)
     (def delEnv (if (null? del) 
      del         
     (multi-extend-env (list 'delegation) (list (interp del env obj caller)) env)))
     (objV fields_box methods_box env delEnv)]
    ;send
    [(send o met-id vals)
     (match (interp o env obj caller)
       [(objV fieldsO methodsO envO delegaEnv) (def l (map (lambda (x)
                                                     (interp x env obj caller)) vals))
                                       (def req-met (lookup-memberEnv met-id (unbox methodsO))) ;; busco el método
                                       (if (not (equal? req-met 'undefined))
                                           (let [(env-met
                                                  (multi-extend-env (car req-met) l envO))] ;; si lo encuentro, extiendo el ambiene uniendo la lista de inputs con las variables
                                             (interp (cdr req-met) env-met (objV fieldsO methodsO envO delegaEnv) caller)) ;; interpetro el cuerpo del method que con el ambiente extendido
                                           (if (null? delegaEnv) ;; si no encuentro el metodo, veo si puedo delegar
                                               (error "method not found") ;; si no puedo delegar
                                               (interp
                                                (send (id 'delegation) met-id vals) ;; si puedo, envio un send al objeto al que le puedo delegar
                                                delegaEnv                        ;; en el ambiente del objeto a delegar
                                                (interp (id 'delegation) delegaEnv) ;;aqui intepreto el objeto al que le voy a delegar
                                                (if (null? caller)               ;; veo si me delegaron a mi esta llamada
                                                    (objV fieldsO methodsO env delegaEnv) ;; si no fue asi, es porque yo estoy delegando
                                                    caller)))                    ;; en caso contrario, es porque me habian delegado y yo subdelego
                                           )])]
    ;this: ~traer el objeto actual~ traer el objeto que hizo la llamada de delegación.
    [(this) (if (not (null? obj)) ; si estamos en un objeto, devolvemos el objeto o el caller
                (if (null? caller) obj caller); si la llamada vino de otro objeto.
                (error "this used outside of an object"))] ;en caso contrario, error de uso.
    ;get: traer un campo de un objeto (dada su id). 
    [(get fld-id) (if (not (null? obj)) ;si estamos en un objeto, buscamos en sus fields.
                      ;lookup devuelve el campo o error de field not found.
                      (let ([req-fld (lookup-memberEnv fld-id (unbox (objV-fields obj)))])
                        (if (equal? 'undefined req-fld)
                            (error "field not found")
                            req-fld))
                      ;si no estabamos en un objeto, levantamos el error de uso..
                      (error "get used outside of an object"))]
    ;set: modificar un campo (dado por id) del objeto actual por el valor resultante de interp ex
    [(set fld-id ex) (if (not (null? obj)) ;si estamos en un objeto, 
                         (let ([unb-fields (unbox (objV-fields obj))]);traemos sus fields
                          (let ([req-fld (lookup-memberEnv fld-id unb-fields)])
                            (if (equal? 'undefined req-fld)
                                (error "field not found")
                                (set-box! (objV-fields obj) ;buscamos y actualizamos el ambiente (o error)
                                (extend-memberEnv fld-id (interp ex env obj caller) unb-fields)))))
                         (error "set used outside of an object"))];si no, error de uso.
    ;shallow copy: una copia de un objeto solo con sus campos y metodos
    ;(sin copiar el objeto de delegación recursivamente).
    [(shallow-copy o)
     (def (objV copy-fields copy-methods copy-env copy-delEnv) (interp o env obj caller))
     (objV (box (unbox copy-fields)) (box (unbox copy-methods)) copy-env copy-delEnv)]
    ;deep copy: similar a shallow-copy, pero incluimos el objeto de
    ;delegación en la copia de manera recursiva.`
    [(deep-copy o)
     (def (objV copy-fields copy-methods copy-env copy-delEnv) (interp o env obj caller))
     (let ([denv
            (if (null? copy-delEnv)
             copy-delEnv
             (multi-extend-env
              (list 'delegation)
              (list (interp (deep-copy (id 'delegation)) copy-delEnv)) copy-delEnv))])
     (objV (box (unbox copy-fields)) (box (unbox copy-methods)) copy-env denv))]                                                                                              
    ))

;; open-val :: Val -> Scheme Value
(define (open-val v)
  (match v
    [(numV n) n]
    [(boolV b) b]
    ))

;; make-val :: Scheme Value -> Val
(define (make-val v)
  (match v
    [(? number?) (numV v)]
    [(? boolean?) (boolV v)]
    ))

;; interp-def :: Def, Env -> Expr
(define (interp-def a-def env)
  (match a-def
    [(my-def id body) (cons id (interp body env))]))

;; run :: s-expr -> Val
(define (run s-expr)
  (interp (parse s-expr) empty-env))

#|
run-val:: s-expr -> Scheme-Val + Val
Versión alternativa de run, que retorna valores de scheme para primitivas y
valores de MiniScheme para clases y objetos
|#
(define (run-val s-expr)
  (define val (interp (parse s-expr) empty-env))
  (match val
    [(numV n) n]
    [(boolV b) b]
    [x x]))
