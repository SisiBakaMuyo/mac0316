#lang plai-typed


; Basic expressions
(define-type ExprC
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [ifC     (c : ExprC) (y : ExprC) (n : ExprC)]
  [seqC    (e1 : ExprC) (e2 : ExprC)]
  [setC    (var : symbol) (arg : ExprC)]
  [letC    (name : symbol) (arg : ExprC) (body : ExprC)]
  [classC  (parent : symbol) (var : symbol) (met1 : ExprC) (met2 : ExprC)]
  [methodC (name : symbol)  (arg : symbol) (body : ExprC)]
  [newC    (name : symbol) (v : ExprC)]
  [sendC   (obj : ExprC) (met : symbol) (arg : ExprC)]
)


; Sugared expressions
(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [seqS    (e1 : ExprS) (e2 : ExprS)]
  [setS    (var : symbol) (arg : ExprS)]
  [letS    (name : symbol) (arg : ExprS) (body : ExprS)]
  [classS  (parent : symbol) (var : symbol) (met1 : ExprS) (met2 : ExprS)]
  [methodS (name : symbol) (arg : symbol) (body : ExprS)]
  [newS    (name : symbol) (v : ExprS)]
  [sendS   (obj : ExprS) (met : symbol) (arg : ExprS)]
)


; Removing the sugar
(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)         (numC n)]
    [idS     (s)         (idC s)]
    [plusS   (l r)       (plusC (desugar l) (desugar r))]
    [multS   (l r)       (multC (desugar l) (desugar r))]
    [bminusS (l r)       (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)         (multC (numC -1) (desugar e))]
    [ifS     (c s n)     (ifC (desugar c) (desugar s) (desugar n))]
    [seqS    (e1 e2)     (seqC (desugar e1) (desugar e2))]
    [setS    (var expr)  (setC  var (desugar expr))]
    [letS    (n a b)     (letC n (desugar a) (desugar b))]
    [classS  (p v m1 m2) (classC p v (desugar m1) (desugar m2))]
    [methodS (n a b)     (methodC n a (desugar b))]
    [newS    (n v)       (newC n (desugar v))]
    [sendS   (o m a)     (sendC (desugar o) m (desugar a))]
))

; We need a new value for the box
(define-type Value
  [numV    (n : number)]
  [methodV (name : symbol) (arg : symbol) (body : ExprC)]
  [classV  (parent : symbol) (var : symbol) (met1 : Value) (met2 : Value)]
  [objectV (classe : Value) (pai : Value) (instVar : Binding)]
)

; Bindings associate symbol with location
(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])

(define ClasseObject
        (classV 'null 'dummy (methodV 'met1 'none (numC 42))
                             (methodV 'met2 'none (numC 42))))

(define ObjetoObject
  (objectV ClasseObject (numV 0) (bind 'none (box (numV 42)))))

; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env (cons (bind 'Object (box ClasseObject)) empty))
(define extend-env cons)


; Find the name of a variable
(define (lookup [for : symbol] [env : Env]) : (boxof Value)
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string for) " was not found"))] ; variable is undefined
            [else (cond
                  [(symbol=? for (bind-name (first env)))   ; found it!
                                 (bind-val (first env))]
                  [else (lookup for (rest env))])]))        ; check in the rest

(define (lookup-method [name : symbol] [obj : Value]) : Value
      (cond
          [(equal? obj ObjetoObject) (error 'lookup-method "mensagem desconhecida")]
          [else (cond
              [(symbol=? name (methodV-name (classV-met1 (objectV-classe obj))))
                              (classV-met1 (objectV-classe obj))]
              [(symbol=? name (methodV-name (classV-met2 (objectV-classe obj))))
                              (classV-met2 (objectV-classe obj))]
              [else (lookup-method name (objectV-pai obj))]
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

; Auxiliary operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "One of the arguments is not a number")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "One of the arguments is not a number")]))

; Interpreter
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    ; Numbers just evaluta to their equivalent Value
    [numC (n) (numV n)]

    ; IDs are retrieved from the Env and unboxed
    [idC (n) (unbox (lookup n env))]

    ; Sum two numbers using auxiliary function
    [plusC (l r) (num+ (interp l env) (interp r env))]

    ; Multiplies two numbers using auxiliary function
    [multC (l r) (num* (interp l env) (interp r env))]

    ; Conditional operator
    [ifC (c s n) (if (zero? (numV-n (interp c env))) (interp n env) (interp s env))]

    ; Sequence of operations
    [seqC (b1 b2) (begin (interp b1 env) (interp b2 env))] ; No side effect between expressions!

    ; Attribution of variables
    [setC (var val) (let ([b (lookup var env)])
                      (begin (set-box! b (interp val env)) (unbox b)))]

    ; Declaration of variable
    [letC (name arg body)
          (let* ([new-bind (bind name (box (interp arg env)))]
                 [new-env (extend-env new-bind env)])
            (interp body new-env))]

    [classC (p v m1 m2) (classV p v (interp m1 env) (interp m2 env))]

    [methodC (n a b) (methodV n a b)]

    [newC (n v)
        (let ([classe (unbox (lookup n env))])
             (objectV
                classe
                (if (equal? (classV-parent classe) (classV-parent ClasseObject))
                   ObjetoObject
                   (interp (newC (classV-parent classe) (numC 0)) env))
                (bind (classV-var classe) (box (interp v env)))))]

    [sendC (o m a)
        (let* ([objeto (interp o env)]
               [objEnv (mount-env objeto)]
               [method (lookup-method m objeto)])

              (interp (methodV-body method)
                 (extend-env (bind (methodV-arg method) (box (interp a env))) objEnv)))]

    ))


; Parser
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         ;[(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))] ; definição
         ;[(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(seq) (seqS (parse (second sl)) (parse (third sl)))]
         [(:=) (setS (s-exp->symbol (second sl)) (parse (third sl)))]
         [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (third sl)))]

         [(class) (classS (s-exp->symbol (second sl))
                          (s-exp->symbol (third sl))
                          (parse (fourth sl))
                          (parse (fourth (rest sl))))]

         [(method) (methodS (s-exp->symbol (second sl))
                            (s-exp->symbol (third sl))
                            (parse (fourth sl)))]

         [(new) (newS (s-exp->symbol (second sl))
                      (parse (third sl)))]

         [(send) (sendS (parse (second sl))
                        (s-exp->symbol (third sl))
                        (parse (fourth sl)))]

         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env))


; Testes
; Os testes a seguir foram fornecidos por outros alunos com autorização prévia:
(test
  (interpS
    '(let ([Wallet
             (class Object money
                    (method credit amount (:= money (+ money amount)))
                    (method debit amount (:= money (- money amount))) )])
       (let ([wallet (new Wallet 0)])
         (seq (send wallet credit 10)
              (send wallet debit 3)))))
  (numV 7))
(test (interpS '(let
                    ([heroi
                      (class Object capa
                        (method aumenta x (+ capa x))
                        (method decresce y (- capa y)))])
                  (let ([batima (new heroi 2)])
                    (send batima aumenta 3))))
      (numV 5))
(test (interpS '(let ([heroi
                      (class Object capa
                        (method aumenta x (+ capa x))
                        (method decresce y (- capa y)))])
                  (let ([antiheroi
                         (class heroi arma
                           (method multiplica a (+ arma a))
                           (method aumenta b (+ (+ arma b) 300)))])
                  (let ([batima (new antiheroi 2)])
                  (let ([coringa (new heroi 5)])
                    (send coringa aumenta 3))))))
      (numV 8))
(test (interpS '(let ([heroi
                      (class Object capa
                        (method aumenta x (+ capa x))
                        (method decresce y (- capa y)))])
                  (let ([antiheroi
                         (class heroi arma
                           (method multiplica a (+ arma a))
                           (method aumenta b (+ (+ arma b) 300)))])
                  (let ([batima (new antiheroi 2)])
                    (send batima decresce 3)))))
      (numV -3))
(test (interpS '(let ([heroi
                      (class Object capa
                        (method aumenta x (+ capa x))
                        (method decresce y (- capa y)))])
                  (let ([antiheroi
                         (class heroi arma
                           (method multiplica a (+ arma a))
                           (method aumenta b (+ (+ arma b) 300)))])
                  (let ([batima (new antiheroi 2)])
                    (send batima aumenta 3)))))
      (numV 305))
(test (interpS '(let
                    ([heroi
                      (class Object capa
                        (method aumenta x (+ capa x))
                        (method decresce y (- capa y)))])
                  (let ([batima (new heroi 2)])
                    (send batima aumenta 3))))
      (numV 5))
(test (interpS '(let ([Wallet
                 (class Object money
                   (method credit amount (:= money (+ money amount)))
                   (method debit amount (:= money (- money amount))))])
                   (let ([Super-Wallet
                          (class Wallet money
                            (method credit-super amount (:= money (+ money (* amount 2))))
                            (method debit-super amount (:= money (- money (* amount 2)))))])
                     (let ([wallet (new Super-Wallet 10)])
                       (seq (send wallet credit 10)
                            (send wallet credit-super 10))))))
      (numV 40))
(test (interpS '(let ([Wallet
                 (class Object money
                   (method credit amount (:= money (+ money amount)))
                   (method debit amount (:= money (- money amount))))])
                   (let ([Super-Wallet
                          (class Wallet money
                            (method credit amount (:= money (+ money (* amount 2))))
                            (method debit-super amount (:= money (- money (* amount 2)))))])
                     (let ([wallet (new Super-Wallet 0)])
                       (seq (send wallet credit 10)
                            (send wallet debit 10))))))
      (numV 10))
(test (interpS '(let ([Wallet
                 (class Object money
                   (method credit amount (:= money (+ money amount)))
                   (method debit amount (:= money (- money amount))))])
            (let ([Wallet2
              (class Wallet moneyf
                (method gasta amount (:= moneyf (let ([saldo (- moneyf amount)])
                                                   (if saldo saldo moneyf))))
                (method recebe amount (:= moneyf (let ([saldo (- money amount)])
                                                   (if saldo
                                                       (seq (:= money saldo)
                                                                  (:= moneyf (+ moneyf amount)))
                                                       moneyf)))))])
              (let ([wallet (new Wallet2 0)])
                (seq (send wallet credit 20)
                     (seq (send wallet recebe 10)
                          (send wallet gasta 2)))))))
      (numV 8))
