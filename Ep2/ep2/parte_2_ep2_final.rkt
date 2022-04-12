#lang plai-typed

;Luis Vitor Zerkowski - 9837201
;Isis Ardisson Logullo - 7577410

#|
 | interpretador simples, com variáveis e funções
 |#

#| primeiro as expressões "primitivas", ou seja, diretamente interpretadas
 |#

(define-type ExprC
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [lamC    (arg : symbol) (body : ExprC)]
  [appC    (fun : ExprC) (arg : ExprC)]
  [ifC     (cond : ExprC) (y : ExprC) (n : ExprC)]
  [consC   (car : ExprC) (cdr : ExprC)]; Creates cell with a pair
  [carC    (pair : ExprC)]; Gets 1st element of a pair
  [cdrC    (pair : ExprC)]; Gets 2nd element of a pair
  [letrecC (var : symbol) (expression : ExprC) (body : ExprC)]
  [quoteC  (sym : symbol)]
  [readloopC ]
  [boolC    (b : boolean)]
  [nullC  ]
  [equal?C (val1 : ExprC) (val2 : ExprC)]
  )
#| agora a linguagem aumentada pelo açúcar sintático
 | neste caso a operação de subtração e menus unário
 |#

(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [lamS    (arg : symbol) (body : ExprS)]
  [appS    (fun : ExprS) (arg : ExprS)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [consS   (car : ExprS) (cdr : ExprS)]
  [carS    (pair : ExprS)]
  [cdrS    (pair : ExprS)]
  [letS    (var : symbol) (exp : ExprS) (body : ExprS)]
  [let*S    (var1 : symbol) (exp1 : ExprS) (var2 : symbol) (exp2 : ExprS) (body : ExprS)]
  [letrecS (var : symbol)  (exp : ExprS)  (body : ExprS)]
  [quoteS  (sym : symbol)]
  [readloopS ]
  [boolS    (b : boolean)]
  [nullS ]
  [equal?S (val1 : ExprS) (val2 : ExprS)]
  )


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [lamS    (a b)      (lamC a (desugar b))]
    [appS    (fun arg)  (appC (desugar fun) (desugar arg))]
    [plusS   (l r)      (plusC (desugar l) (desugar r))]
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c y n)    (ifC (desugar c) (desugar y) (desugar n))]
    [consS   (b1 b2)    (consC (desugar b1) (desugar b2))]
    [carS    (c)        (carC (desugar c))]
    [cdrS    (c)        (cdrC (desugar c))]
    [letS    (v e b)    (appC (lamC v (desugar b)) (desugar e))]
    [let*S    (v1 e1 v2 e2 b)    (appC (lamC v1 (appC (lamC v2 (desugar b) )
                                                      (desugar e2)))
                                       (desugar e1))]
    [letrecS    (v e  b)  (letrecC v (desugar e) (desugar b))]
    [quoteS  (sym) (quoteC sym)]
    [readloopS  () (readloopC)]
    [boolS    (b)             (boolC b)]
    [nullS    ()              (nullC)]
    [equal?S (val1 val2) (equal?C (desugar val1) (desugar val2))]
    ))



; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [consV (car : Promise) (cdr : Promise)]
  [symV (sym : symbol)]
  [boolV    (b : boolean)]
  [suspV (body : ExprC) (env : Env)]
  [nullV ]
  )


; Bindings associate symbol with Boxes
; we need this to be able to change the value of a binding, which is important
; to implement letrec.

(define-type Binding
        [bind (name : symbol) (val : Promise)])


; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


; Storage's operations are similar to Env's
;   bind <-> cell
;   mt-env <-> mt-store
;   extend-env <-> override-store


; lookup changes its return type
(define (lookup [varName : symbol] [env : Env]) : Promise; lookup returns the box, we need this to change the value later
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string varName) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                    [(symbol=? varName (bind-name (first env)))   ; achou!
                     (bind-val (first env))]
                    [else (lookup varName (rest env))])]))        ; vê no resto



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



;Usado em celulas e no ambiente para conter algo que pode ser uma suspensão ou um valor normal. Deve utilizar boxes.
(define-type Promise
    [aPromise (valueBox : (boxof Value))])

;Função auxiliar query-promise para acessar o valor contido numa promise
(define (query-promise [prom : Promise]) : Value
        (let ((theBox (aPromise-valueBox prom)))
          (type-case Value (unbox theBox)
            [suspV (body susp-env)
                  (let* ((finalValue (interp body susp-env)))
                    (begin (set-box! theBox finalValue)
                           finalValue))]
            [else (unbox theBox)]
)))
  


; Return type for the interpreter, Value


(define (interp [a : ExprC] [env : Env] ) : Value
  (type-case ExprC a
    [numC (n) (numV n) ]
    [idC (n)  (unbox (box(query-promise(lookup n env))))]; we need to unbox the value in the environment before using it
    [lamC (a b) (closV a b env) ]
    [boolC (b) (boolV b)]

 
    ; application of function
    [appC (f a)
          (let ((closure (query-promise(aPromise(box(interp f env)))))
                (argvalue a))
            (type-case Value closure
              [closV (parameter body env-closure)
                     (query-promise(aPromise(box(interp body (extend-env (bind parameter (aPromise(box(suspV argvalue env)))) env-closure)))))]
              [else (error 'interp "operation app aplied to non-closure")]
              ))]
   
    ;I left plusC without error-checking
    [plusC (l r) (num+ (query-promise(aPromise(box(interp l env)))) (query-promise(aPromise(box(interp r env)))))]

    ; Multiplies two numbers using auxiliary function
    [multC (l r) (num* (query-promise(aPromise(box(interp l env)))) (query-promise(aPromise(box(interp r env)))))]
    
    ; ifC serializes
    [ifC (c s n)
         (if (boolV-b (query-promise (aPromise (box (interp c env))))) (query-promise (aPromise (box (interp s env)))) (query-promise (aPromise (box (interp n env)))))]


    ; Working with lists
    [consC (car cdr)
           (consV  (aPromise(box(suspV car env))) (aPromise(box(suspV cdr env))))]
    
    [carC (c) (type-case Value (interp c env)
                [consV (car cdr)
                       (query-promise car)]
                [else (error 'interp "car applied to non-cell")]
                )]
    [cdrC (c) (type-case Value (interp c env)
                [consV (car cdr)
                       (query-promise cdr)]
                [else (error 'interp "cdr applied to non-cell")]
                )]
  
     [letrecC (n a b)
      (let* ([mybox (box (nullV))] [new-env (extend-env [bind n (aPromise mybox)] env)])
          (begin (set-box! mybox (suspV a new-env)) (query-promise (aPromise (box (interp b new-env) )))))]
                 
    [quoteC  (s) (symV s)]
    [readloopC () (letrec ( (read-till-end (lambda ()
                                              (let ((input (read)))
                                                (if (and (s-exp-symbol? input )
                                                         (eq? (s-exp->symbol input) '@END))
                                                    (begin (display 'FINISHED-READLOOP)
                                                           (symV  'END_OF_loop))
                                                    (begin (display (query-promise (aPromise (box (interp (desugar (parse input)) env) ))))
                                                           (read-till-end)))))))
                     (read-till-end))]

    [equal?C (e1 e2)
      (boolV (equal? (query-promise (aPromise (box (interp e1 env) ))) (query-promise (aPromise (box (interp e2 env) )))))]

    [nullC  () (nullV)]

   ))


; Parser with funny instructions for boxes
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))] ; pode ser um símbolo livre nas definições de função
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (if (empty? sl)
           (nullS)
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))] ; definição
         [(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(cons) (consS (parse (second sl)) (parse (third sl)))]
         [(car) (carS (parse (second sl)))]
         [(cdr) (cdrS (parse (second sl)))]
         [(quote) (quoteS (s-exp->symbol (second sl)))]
         [(let) (letS (s-exp->symbol (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(let*) (let*S (s-exp->symbol (second sl))
                        (parse (third sl))
                        (s-exp->symbol (fourth sl))
                        (parse (fourth (rest sl)))
                        (parse (fourth (rest (rest sl)))))]
         [(let) (letS (s-exp->symbol (second sl))
                      (parse (third sl))
                      (parse (fourth sl)))]
         [(letrec) (letrecS (s-exp->symbol (second sl))
                            (parse (third sl))
                            (parse (fourth sl)))]
         [(read-loop)(readloopS)]
         [(equal?) (equal?S (parse (second sl)) (parse (third sl)))]
         
        
         [else (error 'parse "invalid list input")])))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env))


; Examples
(interpS '(+ 10 (call (lambda x (car x)) (cons 15 16))))

(interpS '(call (lambda x (+ x 5)) 8))


(interpS '(call (lambda f (call f (~ 32))) (lambda x (- 200 x))))


; Tests
(test (interp (carC (consC (numC 10) (numC 20)))
              mt-env)
      (numV 10))

(appC (lamC 'x (plusC (numC 4) (numC 0)))
      (plusC (numC 4) (numC 0)))