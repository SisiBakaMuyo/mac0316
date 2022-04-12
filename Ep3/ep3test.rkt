#lang plai-typed

;Luis Vitor Zerkowski - 9837201
;Isis Ardisson Logullo - 7577410


#| primeiro as expressões "primitivas", ou seja, diretamente interpretadas
 |#

(define-type ExprC
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [ifC     (cond : ExprC) (y : ExprC) (n : ExprC)]
  [letC (var : symbol) (expression : ExprC) (body : ExprC)]
  [quoteC  (sym : symbol)]
  [readloopC (placeholder : symbol)]
  [nullC]
  [seqC  (statement1 : ExprC) (statement2 : ExprC)]
  [setC  (varName : symbol) (statement : ExprC)]
  [classC  (parent : symbol) (var : symbol) (met1 : ExprC) (met2 : ExprC)]
  [regularMethodC (name : symbol)  (arg : symbol) (body : ExprC)]
  [primitiveMethodC (name : symbol) (primNumber : number)]
  [newC    (name : symbol) (v : ExprC)]
  [sendC   (obj : ExprC) (met : symbol) (arg : ExprC)]
  

  )
#| agora a linguagem aumentada pelo açúcar sintático
 | neste caso a operação de subtração e menus unário
 |#

(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [letS    (var : symbol) (exp : ExprS) (body : ExprS)]
  [quoteS  (sym : symbol)]
  [readloopS (placeholder : symbol)]
  [seqS (statement1 : ExprS) (statement2 : ExprS)]
  [setS (variable : symbol) (statement : ExprS)]
  [newS    (class : symbol) (value : ExprS)]
  [classS  (superClass : symbol) (instVar : symbol) (method1 : ExprS ) (method2 : ExprS)]
  [regularMethodS (name : symbol) (arg : symbol) (body : ExprS)]
  [primitiveMethodS (name : symbol) (primNumber : number)]
  [sendS   (receiver : ExprS) (method : symbol) (arg : ExprS)]
  [nullS  ]
  )


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [plusS   (l r)      (plusC (desugar l) (desugar r))]
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c y n)    (ifC (desugar c) (desugar y) (desugar n))]
    [letS    (v e b)    (letC v (desugar e) (desugar b))]
    [quoteS  (sym) (quoteC sym)]
    [readloopS (s) (readloopC s)]
    [nullS  ()  (nullC)]
    [seqS (st1 st2) (seqC (desugar st1) (desugar st2))]
    [setS (var st)  (setC var (desugar st))]
    [classS  (p v m1 m2) (classC p v (desugar m1) (desugar m2))]
    [regularMethodS (n a b)     (regularMethodC n a (desugar b))]
    [primitiveMethodS (n p) (primitiveMethodC n p)]
    [newS    (n v)       (newC n (desugar v))]
    [sendS   (o m a)     (sendC (desugar o) m (desugar a))]

 
    ))



; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  ;[closV (arg : symbol) (body : ExprC) (env : Env)]
  ;[consV (car : Value) (cdr : Value)]
  [symV (sym : symbol)]
  [nullV ]
  [methodV (name : symbol) (def : MethodDefinition)]
  [classV  (parent : symbol) (var : symbol) (met1 : Value) (met2 : Value)]
  [objectV (classe : Value) (pai : Value) (instVar : Binding)]
  )


; Bindings associate symbol with Values
(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])

(define-type MethodDefinition
  [regularMethod (par : symbol) (body : ExprC)]
  [primitiveMethod (num : number)]
  )

(define ClasseObject
        (classV 'null 'dummy (methodV 'name1 (regularMethod 'met1 (numC 42)))
                             (methodV 'name2 (regularMethod 'met2 (numC 42)))))

(define ObjetoObject
  (objectV ClasseObject (numV 0) (bind 'none (box (numV 42)))))


(define self
  (lambda  (env) ObjetoObject))


(define PrimitiveMethodVector
  (make-vector 2 (lambda ([ x : Value] ) : Value
                   (error 'primitive "invalid primitive method")))); 0
;add primitive 1 for 'mensagemDesconhecida
(vector-set! PrimitiveMethodVector 1
             (lambda ([methodName : Value])
               (type-case Value methodName
                 [symV (symbolValue)
                       (error 'messaging
                              (string-append "mensagemDesconhecida:"
                                             (symbol->string symbolValue)))]
                 [else (error 'wrongArgument
                              "Wrong Argument: primitive 1 should receive a symV")])))


; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


; auxiary functions for messageLookup                                         
(define (lookup [varName : symbol] [env : Env]) : (boxof Value)
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string varName) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                    [(symbol=? varName (bind-name (first env)))   ; achou!
                     (bind-val (first env))]
                    [else (lookup varName (rest env))])]))        ; vê no resto


(define (methodLookup [name : symbol] [obj : Value]) : Value
      (cond
          [(equal? obj (nullV)) (error 'methodLookup "mensagem desconhecida")]
          [else (cond
              [(symbol=? name (methodV-name (classV-met1 (objectV-classe obj))))
                              (classV-met1 (objectV-classe obj))]
              [(symbol=? name (methodV-name (classV-met2 (objectV-classe obj))))
                              (classV-met2 (objectV-classe obj))]
              [else (methodLookup name (objectV-pai obj))]
          )]
      )
)

(define (mount-env [obj : Value]) : Env
     (cond
         [(equal? obj ObjetoObject) empty]
         [else (extend-env
                 (objectV-instVar obj)
                 (mount-env (objectV-pai obj)))]
     )
)

(define (mensagemDesconhecida [msg : symbol]) : Value
                              (error 'erro: (string-append "mensagemDesconhecida:" (symbol->string msg))))



; Primitive operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "Um dos argumentos não é número")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "Um dos argumentos não é número")]))


; Return type for the interpreter, Value


(define (interp [a : ExprC] [objectEnv : Env]) : Value
  (type-case ExprC a
    [nullC () (nullV)]
    [numC (n) (numV n) ]
    [idC (n)  (unbox (lookup n objectEnv))]; cascading search, first in env then in sto
    ;I left plusC without error-checking
    [plusC (l r)
             (let ((left (interp l objectEnv ))
                   (right (interp r objectEnv )))
               (num+ left right))]
    ;multC
    [multC (l r)
           (let ( (left (interp l objectEnv ))
                  (right (interp r objectEnv )))
             ;in this case type cheking is a little different
             (if (numV? left)
                 (if (numV? right)
                     (num* left right)
                     (error 'interp "second argument of multiplication not a number value"))
                 (error 'interp "first argument of multiplication not a number value"))
                 )]
    ; ifC serializes
    [ifC (c s n) (type-case Value (interp c objectEnv )
                   [numV (value)
                        (if (zero? value)
                            (interp n objectEnv )
                            (interp s objectEnv ))]
                   [else (error 'interp "condition not a number")]
                   )]
    [quoteC  (s) (symV s)]
    [readloopC (ph) (letrec ( (read-till-end (lambda ()
                                              (let ( (input (read)))
                                                (if (and (s-exp-symbol? input )
                                                         (eq? (s-exp->symbol input) '@END))
                                                    (begin (display 'FINISHED-READLOOP)
                                                           (symV  'END_OF_loop))
                                                    (begin (display (interp (desugar (parse input)) objectEnv ))
                                                           (read-till-end)))))))
                     (read-till-end))]
    [letC (variable expression body)
          (let ((value (interp expression objectEnv )))
            (interp body
                    (extend-env (bind variable (box value)) objectEnv)
                    ))]
    [seqC (firstCommand secondCommand)
          (begin (interp firstCommand objectEnv)
                 (interp secondCommand objectEnv))]
    [setC  (variableName statement)
           (let ((varBox (lookup variableName objectEnv))
                 (value (interp statement objectEnv)))
             (begin (set-box! varBox value)
                    value))]

    [classC (p v m1 m2) (classV p v (interp m1 objectEnv) (interp m2 objectEnv))]

    [regularMethodC (n a b) (methodV n (regularMethod a b))]

    [primitiveMethodC (n p) (methodV n (primitiveMethod p))]

    [newC (n v)
        (let ([classe (unbox (lookup n objectEnv))])
             (objectV
                classe
                (if (equal? (classV-parent classe) (classV-parent ClasseObject))
                   ObjetoObject
                   (interp (newC (classV-parent classe) (numC 0)) objectEnv))
                (bind (classV-var classe) (box (interp v objectEnv)))))]

    [sendC (o m a)
     ;   (let* ([objeto (interp o objectEnv)]
     ;          [method (methodLookup m objeto)]
                [aux (bind (methodV-def method) (box (interp arg objectEnv)))]
                [new_env (extend-env aux (mount-env objeto))]]

      ;        (interp (methodV-def method) new_env))]

   ; [sendC (o m a)
     ;   (let* ([objeto (interp o objectEnv)]
    ;           [objEnv (mount-env objeto)]
     ;          [method (lookup-method m objeto)])

      ;        (interp (methodV-def method)
      ;           (extend-env (bind (methodV-def method) (box (interp a objectEnv))) objEnv)))]
     
    ))


; Parser with funny instructions for boxes
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))] ; pode ser um símbolo livre nas definições de função
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
          [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(quote) (quoteS (s-exp->symbol (second sl)))]
         [(let) (letS (s-exp->symbol (second sl))
                      (parse (third sl))
                      (parse (fourth sl)))]
          [(set!) (setS (s-exp->symbol (second sl))
                      (parse (third sl)))]
         [(seq) (seqS (parse (second sl))
                      (parse (third sl)))]
         [(class) (classS (s-exp->symbol (second sl))
                          (s-exp->symbol (third sl))
                          (parse (fourth sl))
                          (parse (fourth (rest sl))))]

         [(regularMethod) (regularMethodS (s-exp->symbol (second sl))
                            (s-exp->symbol (third sl))
                            (parse (fourth sl)))]

         [(new) (newS (s-exp->symbol (second sl))
                      (parse (third sl)))]

        ; [(send) (sendS (parse (second sl))
         ;               (s-exp->symbol (third sl))
          ;              (parse (fourth sl)))]
         
        [else (error 'parse "invalid list input")]
         ))]
    [else (error 'parse "invalid input")]
    ))
 

; Facilitator
; Enviromnent needs to be intialzed with the association for the Object class, which needs to be defined elsewhere 
;(define initialObjectEnv (extend-env (bind 'Object (box ObjectClass)) mt-env))
;(define (interpS [s : s-expression]) : Value
;  (interp (desugar (parse s)) initialObjectEnv ))

; Examples
;(interpS '(class Object i (regularMethod m1 x x) (regularMethod m2 x i)))
;(interpS '(let classe1 (class Object i (regularMethod m1 x x) (regularMethod m2 x i))
;            (let object1 (new classe1 1) (send object1 m1 5))))
;(interpS '(let classe1 (class Object i (regularMethod m1 x x) (regularMethod m2 x i))
;            (let object1 (new classe1 1) (send object1 m2 5))))
; no proximo exemplo definimos um novo m1 em uma subclasse, instanciamos e mandamos a mensagem m2 para no novo
;objeto. O interpretador deve voltar o resultado de m1 da subclasse. (
;(interpS '(let classe1 (class Object i (regularMethod m1 x i) (regularMethod m2 x (send self m1 x)))
;            (let classe2 (class classe1 j (regularMethod m1 x (quote subclassregularMethod)) (regularMethod m3 y y))
;              (let object2 (new classe2 200) (send object2 m2 55)))))
;(interpS '(let classe1 (class Object i (regularMethod m1 x i) (regularMethod m2 x (send self m1 x)))
;            (let classe2 (class classe1 j (regularMethod m1 x (quote subclassregularMethod)) (regularMethod m3 y y))
;              (let object2 (new classe2 200) (send object2 m22 55)))))

; Tests
