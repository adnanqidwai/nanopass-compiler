#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)	
(require data/queue)
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Cfun.rkt")
(require "interp.rkt")
(require "type-check-Cfun.rkt")
(require "type-check-Lfun.rkt")
(require "priority_queue.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))

(define (shrink-exp e)
  (match e
    [(Prim 'and (list e1 e2)) (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or (list e1 e2)) (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(Prim op es) (Prim op (for/list ([e es]) (shrink-exp e)))]
    [(Let x rhs body) (Let x (shrink-exp rhs) (shrink-exp body))]
    [(If cnd thn els) (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
    [(SetBang x es) (SetBang x (shrink-exp es))]
    [(Begin es body) (Begin (for/list ([e es]) (shrink-exp e)) (shrink-exp body))]
    [(WhileLoop cnd body) (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [(Apply fun args) (Apply (shrink-exp fun) (for/list ([e args]) (shrink-exp e)))]
    [_ e]))
  
(define (shrink-def def)
  (match def
    [(Def name params rt info body) (Def name params rt info (shrink-exp body))]))

(define (shrink p)
  (match p
    [(ProgramDefsExp info defs body) 
      (let* ([main-fun (Def 'main '() 'Integer '() body)]
             [defs (cons main-fun defs)])
              (ProgramDefs info (for/list ([def defs]) (shrink-def def))))]))
              
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Let x e body) 
       (define xsym (gensym x))
       (define new-env (dict-set env x xsym))
       (Let xsym ((uniquify-exp env) e) ((uniquify-exp new-env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(If exp1 exp2 exp3)
       (If ((uniquify-exp env) exp1) ((uniquify-exp env) exp2) ((uniquify-exp env) exp3))]
      [(SetBang x es) (SetBang (dict-ref env x) ((uniquify-exp env) es))]
      [(Begin es body) (Begin (for/list ([e es]) ((uniquify-exp env) e)) ((uniquify-exp env) body))]
      [(WhileLoop cnd body) (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(Apply fun args) (Apply ((uniquify-exp env) fun) (for/list ([e args]) ((uniquify-exp env) e)))]
      [_ e])))

(define (uniquify-def def env)
  (match def
    [(Def name params rt info body) 
      (define new-params (for/list ([param params])
                                  (let ([param-name 
                                         (match param
                                           [`(,name : ,type) name])])
                              (dict-set! env param-name (gensym param-name)))
                              (match param
                                [`(,name : ,type) (let ([new-param-name (dict-ref env name)])
                                                    `(,new-param-name : ,type))])))
      (Def name new-params rt info ((uniquify-exp env) body))]))

(define (build-uniquify-env defs)
  (let* ([env (make-hash)])
    (for ([def defs])
      (match def
        [(Def name params rt info body)
          (when (not (eq? name 'main))
            (dict-set! env name name))]))
            env))

(define (uniquify p)
  (match p
    [(ProgramDefs info defs)
      (let ([env (build-uniquify-env defs)])
        (ProgramDefs info (for/list ([def defs])
                            (uniquify-def def env))))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (reveal-functions-exp env)
  (lambda (e)
    (match e
      [(Var x) (if (dict-has-key? env x)
              (FunRef x (dict-ref env x))
              (Var x))]
      [(Let x e body) (Let x ((reveal-functions-exp env) e) ((reveal-functions-exp env) body))]
      [(Prim op es) (Prim op (for/list ([e es]) ((reveal-functions-exp env) e)))]
      [(If e1 e2 e3) (If ((reveal-functions-exp env) e1) ((reveal-functions-exp env) e2) ((reveal-functions-exp env) e3))]
      [(SetBang x e) (SetBang x ((reveal-functions-exp env) e))]
      [(Begin es e) (Begin (for/list ([esp es]) ((reveal-functions-exp env) esp)) ((reveal-functions-exp env) e))]
      [(WhileLoop cnd e) (WhileLoop ((reveal-functions-exp env) cnd) ((reveal-functions-exp env) e))]
      [(HasType expr type) (HasType ((reveal-functions-exp env) expr) type)]
      [(Apply fun args)
       (Apply ((reveal-functions-exp env) fun) (for/list ([arg args]) ((reveal-functions-exp env) arg)))]
      [_ e])))

(define (reveal-functions-defs defs function-info)
  (map
   (lambda (x)
     (match x
       [(Def name params rty info body)
        (Def name params rty info ((reveal-functions-exp function-info) body))]))
   defs))

(define (reveal-functions p)
  (match p
    [(ProgramDefs info defs)
     (let ([function-info
            (map
             (lambda (x)
               (match x
                 [(Def name params _ _ _) (cons name (length params))]))
             defs)])
       (ProgramDefs info (reveal-functions-defs defs function-info)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (limit-body-apply args)
  (match args
    [(list p1 p2 p3 p4 p5 ps ..2)
      (list p1 p2 p3 p4 p5 (Prim 'vector ps))]
    [_ args]))

(define (limit-body env)
  (lambda (e)
    (match e
      [(Var x) (if (dict-has-key? env x)
              (dict-ref env x)
              (Var x))]
      [(FunRef x n) (if (dict-has-key? env x)
              (dict-ref env x)
              (FunRef x n))]
      [(Let x e body)
        (Let x
        ((limit-body env) e)
        ((limit-body env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((limit-body env) e)))]
      [(If e1 e2 e3)
       (If ((limit-body env) e1) ((limit-body env) e2) ((limit-body env) e3))]
      [(SetBang x e)
       (SetBang x ((limit-body env) e))]
      [(Begin es e)
       (Begin (for/list ([esp es]) ((limit-body env) esp)) ((limit-body env) e))]
      [(WhileLoop cnd e)
       (WhileLoop ((limit-body env) cnd) ((limit-body env) e))]
      [(HasType expr type) (HasType ((limit-body env) expr) type)]
      [(Apply fun args)
       (Apply
        ((limit-body env) fun)
        (map (limit-body env) (limit-body-apply args)))]
      [_ e])))

(define (get-name-from-param param)
  (match param
    [`(,x : ,t) x]))

(define (limit-body-create-env params vector-name)
  (match params
    [(list p1 p2 p3 p4 p5 ps ..2)
      (for/list 
        ([i (in-range 0 (length ps))]
         [p ps])
        (cons 
          (get-name-from-param p)
          (Prim 'vector-ref (list (Var vector-name) (Int i)))))]
    [_ '()]))

(define (build-type-from-params params)
  (cons
   'Vector
   (map
    (lambda (x)
      (match x
        [`(,x : ,typ) typ]))
    params)))

(define (limit-types typ)
  (match typ
    [(list args ... '-> result ...)
     (append
      (limit-types
       (match args
         [(list p1 p2 p3 p4 p5 ps ..2)
          (list p1 p2 p3 p4 p5 (cons 'Vector ps))]
         [_ args]))
      (list '->)
      (limit-types result))]
    [(list args ...) (map limit-types args)]
    [_ typ]))

(define (limit-params params vector-name)
  (let
      ([args (match params
               [(list p1 p2 p3 p4 p5 ps ..2)
                (list p1 p2 p3 p4 p5 `(,vector-name : ,(build-type-from-params ps)))]
               [_ params])])
    (map
     (lambda (arg)
       (match arg
         [`(,arg : ,typ)
          `(,arg : ,(limit-types typ))]))
     args)))

(define (limit-defs defs)
  (map (lambda (def)
         (let ([vector-name (gensym 'param-vector)])
           (match def
             [(Def name params rty info body)
              (Def
               name
               (limit-params params vector-name)
               (limit-types rty)
               info
               ((limit-body (limit-body-create-env params vector-name)) body))])))
       defs))

(define (limit-functions p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (limit-defs defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; running the HasType pass before this stage basically
(define (combine-lets elem-names elems body)
  (if (empty? elem-names)
    body
    (Let (car elem-names) (car elems) (combine-lets (cdr elem-names) (cdr elems) body))))

(define (expose-allocation-exp e)
  (match e
    [(Prim op args)
      (Prim op (for/list ([arg args]) (expose-allocation-exp arg)))]
    [(Let x rhs body)
      (Let x (expose-allocation-exp rhs) (expose-allocation-exp body))]
    [(If cnd thn els) 
      (If (expose-allocation-exp cnd) (expose-allocation-exp thn) (expose-allocation-exp els))]
    [(SetBang x exp)
      (SetBang x (expose-allocation-exp exp))]
    [(Begin es body)
      (Begin (for/list ([e es]) (expose-allocation-exp e)) (expose-allocation-exp body))]
    [(WhileLoop cnd e)
      (WhileLoop (expose-allocation-exp cnd) (expose-allocation-exp e))]
    [(Apply fun args)
      (Apply (expose-allocation-exp fun) (for/list ([arg args]) (expose-allocation-exp arg)))]
    [(HasType (Prim 'vector elems) type)
      (define allocated-elems (for/list ([elem elems]) (expose-allocation-exp elem)))
      (define elem-names (for/list ([elem allocated-elems]) (gensym 'elem)))

      (define vector-len (length allocated-elems))
      (define vector-space (+ 8 (* 8 vector-len)))
      (define vector-name (gensym 'vector))
      
      (define set-vector-elems
        (for/list ([i (in-range vector-len)])
          (Prim 'vector-set! (list (Var vector-name) (Int i) (Var (list-ref elem-names i))))))
      
      (define collect-vector-space
        (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int vector-space))) (GlobalValue 'fromspace_end)))
            (Void)
            (Collect vector-space)))
      
      (define body
        (Let (gensym '_) collect-vector-space
          (Let vector-name (Allocate vector-len type)
            (Begin
              set-vector-elems
              (Var vector-name)))))
      
      (combine-lets elem-names allocated-elems body)]
    [(HasType exp type) (HasType (expose-allocation-exp exp) type)]
    [_ e]))

(define (expose-allocation p)
  (match p
    [(ProgramDefs info defs)
      (ProgramDefs info (for/list ([def defs])
                          (match def
                            [(Def name params rt info body)
                              (Def name params rt info (expose-allocation-exp body))])))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; return all the variables that occur in the left hand side of a set!
(define (collect-set! e)
  (match e
    [(Prim op es) (for/fold ([s (set)]) ([e es]) (set-union s (collect-set! e)))]
    [(Let _ rhs body) (set-union (collect-set! rhs) (collect-set! body))]
    [(If cnd thn els) (set-union (collect-set! cnd) (set-union (collect-set! thn) (collect-set! els)))]
    [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
    [(Begin es body) (set-union (for/fold ([s (set)]) ([e es]) (set-union s (collect-set! e))) (collect-set! body))]
    [(WhileLoop cnd body) (set-union (collect-set! cnd) (collect-set! body))]
    [(Apply fun args) (set-union (collect-set! fun) (for/fold ([s (set)]) ([e args]) (set-union s (collect-set! e))))]
    [_ (set)]))

;; change the get of mutable variables to GetBang
(define ((uncover-get!-exp set!-vars) e)
  (match e
    [(Var x) 
      (if (set-member? set!-vars x)
        (GetBang x)
        (Var x))]
    [(Prim op es) (Prim op (for/list ([e es]) ((uncover-get!-exp set!-vars) e)))]
    [(Let x rhs body) (Let x ((uncover-get!-exp set!-vars) rhs) ((uncover-get!-exp set!-vars) body))]
    [(If cnd thn els) (If ((uncover-get!-exp set!-vars) cnd) ((uncover-get!-exp set!-vars) thn) ((uncover-get!-exp set!-vars) els))]
    [(SetBang var rhs) (SetBang var ((uncover-get!-exp set!-vars) rhs))]
    [(Begin es body) (Begin (for/list ([e es]) ((uncover-get!-exp set!-vars) e)) ((uncover-get!-exp set!-vars) body))]
    [(WhileLoop cnd body) (WhileLoop ((uncover-get!-exp set!-vars) cnd) ((uncover-get!-exp set!-vars) body))]
    [(Apply fun args) (Apply ((uncover-get!-exp set!-vars) fun) (for/list ([e args]) ((uncover-get!-exp set!-vars) e)))]
    [_ e]))

(define (uncover-get! p)
  (match p
    [(ProgramDefs info defs)
      (ProgramDefs info (for/list ([def defs])
                          (match def
                            [(Def name params rt info body)
                              (Def name params rt info ((uncover-get!-exp (collect-set! body)) body))])))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; applied to sub-expressions that need to become atomic expressions
;; TODO: Make the code for Prim cases cleaner and also look into how exatly make-lets works
(define (collect-env es)
  (match es
    ['() (list '() '())]
    [(list ast rst ...)
     (match (rco-atm ast)
       [(list atm env)
        (match (collect-env rst)
          [(list atm-ret env-ret)
           (list
            (cons atm atm-ret)
            (append env env-ret))])])]))

(define (create-tmp-var)
  (gensym "tmp"))

(define (create-as-tmp-exp ast)
  (let ([tmp-var (create-tmp-var)])
    (list
     (Var tmp-var)
     (list (list tmp-var (rco-exp ast))))))

; Given a AST, convert it into an atom.
; Returns (list atom environment)
(define (rco-atm ast)
  (match ast
    [(Int n) (list (Int n) '())]
    [(Bool n) (list (Bool n) '())]
    [(Var n) (list (Var n) '())]
    [(Void) (list (Void) '())]
    [(Let x e body)
     (match (rco-atm body)
       [(list atm env)
        (list atm (append (list (list x (rco-exp e))) env))])]
    [(Prim op es) (create-as-tmp-exp ast)]
    [(If e1 e2 e3) (create-as-tmp-exp ast)]
    [(GetBang x) (create-as-tmp-exp ast)]
    [(SetBang var exp) (create-as-tmp-exp ast)]
    [(Begin exp-lst exp) (create-as-tmp-exp ast)]
    [(WhileLoop cnd exp) (create-as-tmp-exp ast)]
    [(Collect _) (create-as-tmp-exp ast)]
    [(Allocate _ _) (create-as-tmp-exp ast)]
    [(GlobalValue _) (create-as-tmp-exp ast)]
    [(Apply _ _) (create-as-tmp-exp ast)]
    [(FunRef _ _) (create-as-tmp-exp ast)]))

(define (create-let-from-env env body)
  (match env
    ['() body]
    [(list (list var e) more ...)
     (Let var e (create-let-from-env more body))]))

(define (rco-exp ast)
  (match ast
    [(Var x) ast]
    [(FunRef x n) ast]
    [(Int x) ast]
    [(Bool x) ast]
    [(Void) ast]
    [(Collect _) ast]
    [(Allocate _ _) ast]
    [(GlobalValue _) ast]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es)
     (match (collect-env es)
       [(list atm-list env)
        (create-let-from-env env (Prim op atm-list))])]
    [(If e1 e2 e3) (If (rco-exp e1) (rco-exp e2) (rco-exp e3))]
    [(GetBang var) (Var var)]
    [(SetBang var exp) (SetBang var (rco-exp exp))]
    [(Begin exp-lst exp)
     (Begin
      (for/list ([exp-atm exp-lst])
        (rco-exp exp-atm))
      (rco-exp exp))]
    [(WhileLoop cnd exp) (WhileLoop (rco-exp cnd) (rco-exp exp))]
    [(Apply fun args)
     (match (collect-env args)
       [(list atm-list env)
        (match
            (collect-env (list fun))
          [(list (list fun-atm) fun-env)
           (create-let-from-env (append env fun-env) (Apply fun-atm atm-list))])])]))

(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info
                  (map
                   (lambda (def)
                     (match def
                       [(Def name params rty info body)
                        (Def name params rty info (rco-exp body))]))
                   defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define basic-blocks (list))

(define (func-start-block-name name)
  (string->symbol (string-append (symbol->string name) "start")))

(define (func-conc-block-name name)
  (string->symbol (string-append (symbol->string name) "conclusion")))

(define (create-block tail)
  (match tail
    [(Goto label) (Goto label)]
    [_ (let ([label (gensym 'block)])
         (set! basic-blocks (cons (cons label tail) basic-blocks))
         (Goto label))]))

; Check if a Prim op is a cmp.
(define (is-prim-cmp op)
  (or (equal? op 'eq?)
      (equal? op '<)
      (equal? op '<=)
      (equal? op '>)
      (equal? op '>=)))

(define (explicate-effect e cont)
  (match e
    [(Var x) cont]
    [(FunRef x n) cont]
    [(Int n) cont]
    [(Bool n) cont]
    [(Void) cont]
    [(Collect _) (Seq e cont)]
    [(Allocate _ _) (Seq e cont)]
    [(GlobalValue _) (Seq e cont)]
    [(Let y rhs body)
     (explicate-assign rhs y (explicate-effect body cont))]
    [(Prim 'read es) (Seq e cont)]
    [(Prim 'vector-set! es) (Seq e cont)]
    [(Prim op es) cont]
    [(If cnd thn els)
     (let ([cont-goto (create-block cont)])
       (explicate-pred cnd
                       (explicate-effect thn cont-goto)
                       (explicate-effect els cont-goto)))]
    [(WhileLoop cnd body)
     (let* ([loop-label (gensym 'loop)]
            [cont-goto (create-block cont)]
            [loop-block
             (explicate-pred cnd
                             (create-block (explicate-effect body (Goto loop-label)))
                             (create-block cont-goto))])
       (set! basic-blocks
             (cons (cons loop-label loop-block) basic-blocks))
       (Goto loop-label))]
    [(Begin es body)
     (let ([cont-body (explicate-effect body cont)])
       (foldr explicate-effect cont-body es))]
    [(SetBang var rhs) (explicate-assign rhs var cont)]
    [(Apply fun args) (Seq (Call fun args) cont)]
    [else (error "explicate-effect unhandled case" e)]))

; `thn`, `els` are assumed to be tails i.e. they are
; already passed through explicate-tail.
(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x)
     (IfStmt (Prim 'eq? (list cnd (Bool #t)))
             (create-block thn)
             (create-block els))]
    [(Let x rhs body)
     (explicate-assign rhs x (explicate-pred body thn els))]
    [(Prim 'not (list e))
     (explicate-pred e els thn)]
    [(Prim op es) #:when (is-prim-cmp op)
                  (IfStmt (Prim op es)
                          (create-block thn)
                          (create-block els))]
    [(Prim op args)
     (let ([tmp-var (create-tmp-var)])
        (explicate-assign cnd tmp-var
                          (IfStmt (Prim 'eq? (list (Var tmp-var) (Bool #t)))
                                  (create-block thn)
                                  (create-block els))))]
    [(Apply fun args)
     (let ([tmp-var (create-tmp-var)])
        (explicate-assign cnd tmp-var
                          (IfStmt (Prim 'eq? (list (Var tmp-var) (Bool #t)))
                                  (create-block thn)
                                  (create-block els))))]
    [(Begin es body)
     (let* ([tmp-var (create-tmp-var)]
            [tail-body
             (explicate-assign
              body
              tmp-var
              (explicate-pred (Var tmp-var) thn els))])
       (foldr explicate-effect tail-body es))]

    [(Bool b) (if b thn els)]
    ; Push cnd^ up and use thn^ and els^ as conditions for branches.
    [(If cnd^ thn^ els^)
     ; Create blocks for `thn` and `els` to prevent duplicates.
     (let ([thn-goto (create-block thn)]
           [els-goto (create-block els)])
       (explicate-pred cnd^
                       (explicate-pred thn^ thn-goto els-goto)
                       (explicate-pred els^ thn-goto els-goto)))]
    [else (error "explicate-pred unhandled case" cnd)]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(FunRef x n) (Return (FunRef x n))]
    [(Int n) (Return (Int n))]
    [(Bool n) (Return (Bool n))]
    [(Void) (Return (Void))]
    [(Collect _) (Seq e (Return (Void)))]
    [(Allocate _ _) (Seq e (Return (Void)))]
    [(GlobalValue _) (Seq e (Return (Void)))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(Prim op es) (Return (Prim op es))]
    [(If cnd thn els)
     (explicate-pred cnd (explicate-tail thn) (explicate-tail els))]
    [(WhileLoop cnd body)
     (let* ([loop-label (gensym 'loop)]
            [loop-block
             (explicate-pred cnd
                             (create-block (explicate-effect body (Goto loop-label)))
                             (create-block (Return (Void))))])
       (set! basic-blocks
             (cons (cons loop-label loop-block) basic-blocks))
       (Goto loop-label))]
    [(Begin es body)
     (let ([tail-body (explicate-tail body)])
       (foldr explicate-effect tail-body es))]
    [(SetBang var rhs) (explicate-assign rhs var (Return (Void)))]
    [(Apply fun args) (TailCall fun args)]
    [else (error "explicate-tail unhandled case" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(FunRef y n) (Seq (Assign (Var x) (FunRef y n)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool n) (Seq (Assign (Var x) (Bool n)) cont)]
    [(Void) (Seq (Assign (Var x) (Void)) cont)]
    [(Allocate _ _) (Seq (Assign (Var x) e) cont)]
    [(GlobalValue _) (Seq (Assign (Var x) e) cont)]
    [(Collect _) (Seq e (explicate-assign (Void) x cont))]
    [(Let y rhs body)
     (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd thn els)
     (let ([cont-goto (create-block cont)])
       (explicate-pred cnd
                       (explicate-assign thn x cont-goto)
                       (explicate-assign els x cont-goto)))]
    [(WhileLoop cnd body)
     (let* ([loop-label (gensym 'loop)]
            [cont-goto (create-block cont)]
            [loop-block
             (explicate-pred cnd
                             (create-block (explicate-effect body (Goto loop-label)))
                             (create-block (explicate-assign (Void) x cont-goto)))])
       (set! basic-blocks
             (cons (cons loop-label loop-block) basic-blocks))
       (Goto loop-label))]
    [(Begin es body)
     (let ([cont-body (explicate-assign body x cont)])
       (foldr explicate-effect cont-body es))]
    [(SetBang var rhs) (explicate-assign rhs var (Seq (Assign (Var x) (Void)) cont))]
    [(Apply fun args) (Seq (Assign (Var x) (Call fun args)) cont)]
    [else (error "explicate-assign unhandled case" e)]))

(define (create-start-block-label name)
  (string->symbol (string-append (symbol->string name) "_start")))

(define (create-conclude-block-label name)
  (string->symbol (string-append (symbol->string name) "_conclusion")))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info
                  (map
                   (lambda (def)
                     (set! basic-blocks '())
                     (match def
                       [(Def name params rty info body)
                        (Def name params rty info
                             (cons
                              (cons
                               (create-start-block-label name)
                               (explicate-tail body))
                              basic-blocks))]))
                   defs))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-op-name prim)
  (match prim
    [(Prim '+ (list e1 e2)) 'addq]
    [(Prim '- (list e1 e2)) 'subq]
    [(Prim '- (list e1)) 'negq]))

(define (get-cmp-set-op op)
  (match op
    ['eq? 'sete]
    ['< 'setl]
    ['<= 'setle]
    ['> 'setg]
    ['>= 'setge]))

(define (type-mask type [mask 0])
  (match type
    [(list 'Vector) mask]
    [(list 'Vector (list 'Vector _ ...) more ...)
     (type-mask (cons 'Vector more)
                (bitwise-ior 1 (arithmetic-shift mask 1)))]
    [(list 'Vector _ more ...)
     (type-mask (cons 'Vector more) (arithmetic-shift mask 1))]))

(define (calculate-tag len type)
  (bitwise-ior 1
               (arithmetic-shift len 1)
               (arithmetic-shift (type-mask type) 7)))

(define (func-args-regs) (list 'rdi 'rsi 'rdx 'rcx 'r8 'r9))

(define (regs-args-func)
  (for/list ([reg (in-list (func-args-regs))])
    (list reg (Reg reg))))

(define (set-args->regs args) 
  (for/list ([reg regs-args-func]
             [arg args])
            (Instr 'movq (list (select-atm arg) reg))))

(define (select-atm atm)
  (match atm
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [(Reg r) (Reg r)]
    [(Void) (Imm 0)]
    [(ByteReg r) (ByteReg r)]
    [(Bool b) (if b (Imm 1) (Imm 0))]))

(define
 (select-assign x e)
  (match e
    [atm 
        #:when (atm? atm)
         (list (Instr 'movq (list (select-atm atm) x)))]

    [(GlobalValue var)
     (list
      (Instr 'movq (list (Global var) x)))]

    [(Prim 'not (list e1))
        (if (equal? e1 x)
            (list (Instr 'xorq (list (Imm 1) x)))
            (list
                (Instr 'movq (list (select-atm e1) x))
                (Instr 'xorq (list (Imm 1) x))))]

    [(Prim 'read '())
     (list
      (Callq 'read_int 0)
      (Instr 'movq (list (Reg 'rax) (select-atm x))))]

    [(FunRef fun args)
     (list 
      (Instr 'leaq (list (Global fun) x)))]

    [(Call fun args)
     (append
      (select-stmt e)
      (list (Instr 'movq (list (Reg 'rax) x))))]

    [(Prim 'vector-ref (list name (Int idx)))
     (list
      (Instr 'movq (list (select-atm name) (Reg 'r11)))
      (Instr 'movq (list (Deref 'r11 (* 8 (add1 idx))) (select-atm x))))]

    [(Prim 'vector-set! (list name (Int idx) var))
     (list
      (Instr 'movq (list (select-atm name) (Reg 'r11)))
      (Instr 'movq (list (select-atm var) (Deref 'r11 (* 8 (add1 idx)))))
      (Instr 'movq (list (Imm 0) (select-atm x))))]

    [(Prim 'vector-length (list name))
     (list
      (Instr 'movq (list (select-atm name) (Reg 'r11)))
      (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
      (Instr 'sarq (list (Imm 1) (Reg 'rax)))
      (Instr 'andq (list (Imm 63) (Reg 'rax)))
      (Instr 'movq (list (Reg 'rax) (select-atm x))))]

    [(Allocate len type)
     (list
      (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
      (Instr 'addq (list (Imm (* 8 (add1 len))) (Global 'free_ptr)))
      (Instr 'movq (list (Imm (calculate-tag len type)) (Deref 'r11 0)))
      (Instr 'movq (list (Reg 'r11) (select-atm x))))]

    [(Prim op (list e1))
        (if (equal? e1 x)
            (list (Instr (get-op-name e) (list (select-atm x))))
            (list
                (Instr 'movq (list (select-atm e1) (select-atm x)))
                (Instr (get-op-name e) (list (select-atm x)))))]

    [(Prim op (list e1 e2))
        (cond 
            [(equal? e2 x)
                (list 
                    (Instr (get-op-name e) (list (select-atm e1) x))
                    (Instr (get-op-name e) (list x x)))]
            [(is-prim-cmp op) 
                (list
                    (Instr 'cmpq (list (select-atm e2) (select-atm e1)))
                    (Instr (get-cmp-set-op op) (list (ByteReg 'al)))
                    (Instr 'movzbq (list (Reg 'al) (select-atm x))))]                  
            [else (list
                    (Instr 'movq (list (select-atm e1) (select-atm x)))
                    (Instr (get-op-name e) (list (select-atm e2) (select-atm x))))])]))


(define (select-stmt stmt)
  (match stmt
    [(Assign x e) (select-assign x e)]
    [(Return e) (select-assign (Reg 'rax) e)]
    [(Prim 'read '())
     (list (Callq 'read_int 0))]
    [(Prim 'vector-set! (list name (Int idx) x))
     (list
      (Instr 'movq (list (select-atm name) (Reg 'r11)))
      (Instr 'movq (list (select-atm x) (Deref 'r11 (* 8 (add1 idx))))))]
    [(Collect size)
     (list
      (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
      (Instr 'movq (list (Imm size) (Reg 'rsi)))
      (Callq 'collect 2))]
    [(Call fun args)
     (append 
      (set-args->regs args)
      (list (IndirectCallq fun (length args))))]))

(define (get-cmp-cnd op)
  (match op
    ['eq? 'e]
    ['< 'l]
    ['<= 'le]
    ['> 'g]
    ['>= 'ge]))

(define (select-if cnd thn els)
    (match cnd
        [(Prim op (list e1 e2)) 
            #:when (is-prim-cmp op)
            (list (Instr 'cmpq (list (select-atm e2) (select-atm e1)))
                    (JmpIf (get-cmp-cnd op) (match thn [(Goto label) label]))
                    (Jmp (match els [(Goto label) label])))]))
                    
(define (convert-to-regs names) (for/list ([reg names]) (Reg reg)))
(define function-call-list (convert-to-regs (list 'rdi 'rsi 'rdx 'rcx 'r8 'r9)))


(define (select-tail t [f-name 'main])
  (match t
    [(Return x) (append (select-stmt t) (list (Jmp (func-conc-block-name f-name))))]
    [(Seq assign tail) (append (select-stmt assign) (select-tail tail))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt cnd thn els) (select-if cnd thn els)]
    [(TailCall fun args)
     (append
      (for/list ([reg function-call-list]
                 [arg args])
        (Instr 'movq (list (select-atm arg) reg)))
      (list (TailJmp fun (length args))))]))

(define (select-block params name)
  (lambda (x)
    (let ([call-list
           (if (eq? (car x) (func-start-block-name name))
               (for/list ([reg regs-args-func]
                          [param params])
                 (Instr 'movq (list reg (Var (car param)))))
               '())])
      (cons (car x) (Block '() (append call-list (select-tail (cdr x) name)))))))

(define (select-defs-map defs)
  (map
   (lambda (def)
     (match def
       [(Def name params ret-typ info body)
          (Def name '() 'Integer (dict-set info 'num-params (length params))
            (map (select-block params name) body))]))
   defs))

(define (select-instructions p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (select-defs-map defs))]))
                           
;;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define caller-saved (list (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)))
(define callee-saved (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15)))
(define pass-args (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))

(define (uncover-arg arg)
  (match arg
    [(Reg _) (set arg)]
    [(Var _) (set arg)]
    [_ (set)]))

(define (uncover-write instr)
  (match instr
    [(Instr (or 'addq 'subq 'movq 'xorq 'set 'movzbq 'leaq) `(,_ ,arg2)) (uncover-arg arg2)]
    [(Instr 'negq `(,arg)) (uncover-arg arg)]
    [(Callq _ _) (list->set caller-saved)]
    [(IndirectCallq _ _) (list->set caller-saved)]
    [_ (set)]))

(define (uncover-read instr)
  (match instr
    [(Instr (or 'addq 'subq 'xorq 'cmpq) `(,arg1 ,arg2)) (set-union (uncover-arg arg1) (uncover-arg arg2))]
    [(Instr 'negq `(,arg)) (uncover-arg arg)]
    [(Instr (or 'movq 'movzbq) `(,arg1 ,_)) (uncover-arg arg1)]
    [(Callq _ num) (list->set (take pass-args num))]
    [(IndirectCallq arg num) (set-union (uncover-arg arg) (list->set (take pass-args num)))]
    [(TailJmp arg num) (set-union (uncover-arg arg) (list->set (take pass-args num)))]
    [_ (set)]))

(define (find-dep block)
  (match block
    [(Block info instrs)
      (for/list ([instr instrs])
        (match instr
          [(Jmp label) label]
          [(JmpIf _ label) label]
          [(TailJmp label _) label]
          [_ (list)]))]))

(define (uncover-live-instrs instrs live-after-sets)
  (match instrs
    [`() live-after-sets]
    [(or `(,(Jmp label) . ,rest) `(,(JmpIf _ label) . ,rest) `(,(TailJmp label _) . ,rest))
      (let* ([live-after (car live-after-sets)]
            [live-before live-after]
            [live-after-sets (cons live-before live-after-sets)])
        (uncover-live-instrs rest live-after-sets))]
    [`(,instr . ,rest)
      (let* ([live-after (car live-after-sets)]
            [writes (uncover-write instr)]
            [reads (uncover-read instr)]
            [live-before (set-union (set-subtract live-after writes) reads)]
            [live-after-sets (cons live-before live-after-sets)])
          (uncover-live-instrs rest live-after-sets))]
    [instr
      (let* ([live-after (car live-after-sets)]
            [writes (uncover-write instr)]
            [reads (uncover-read instr)]
            [live-before (set-union (set-subtract live-after writes) reads)]
            [live-after-sets (cons live-before live-after-sets)])
          live-after-sets)]))

(define (build-cfg label-blocks)
  (let* ([edge-list (for/fold ([edges '()]) 
                              ([label-block label-blocks])
                                (let* ([label (car label-block)]
                                      [deps (find-dep (cdr label-block))]
                                      [edge-blocks (for/fold ([edge-pairs '()]) 
                                                              ([dep deps])
                                                              (if (not (empty? dep)) 
                                                               (cons (list label dep) edge-pairs) 
                                                               edge-pairs))])
                                        (append edge-blocks edges)))])
        (make-multigraph edge-list)))

(define (analyze-dataflow G transfer bottom join)
  (define mapping (make-hash))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (dict-set! mapping 'conclusion (set (Reg 'rax) (Reg 'rsp)))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (if (not (eq? v 'conclusion))
      (enqueue! worklist v)
      (void)))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
    (define node (dequeue! worklist))
    (define input (for/fold ([state bottom])
                          ([pred (in-neighbors trans-G node)])
                    (join state (dict-ref mapping pred))))
    (define output (transfer node input))
    (cond [(not (equal? output (dict-ref mapping node)))
           (dict-set! mapping node output)
           (for ([v (in-neighbors G node)])
              (enqueue! worklist v))]))
  mapping)

(define uncovered-blocks (make-hash))

(define (uncover-live-block block label live-after-sets)
  (match block
    [(Block info instrs)
      (let* ([live-after-sets (list live-after-sets)]
             [live-after-sets (uncover-live-instrs (reverse instrs) live-after-sets)]
             [updated-block (Block (dict-set info 'live-after live-after-sets) instrs)])
        (set! uncovered-blocks (dict-set uncovered-blocks label updated-block))
        live-after-sets)]))

(define (transfer name)
  (lambda (label live-after-set)
    (let* ([block (dict-ref uncovered-blocks label)]
           [live-after-sets (uncover-live-block block label live-after-set)])
      (if (equal? label (func-conc-block-name name))
        (set)
        (car live-after-sets)))))

(define (uncover-live-blocks label-blocks name)
  (set! uncovered-blocks label-blocks)
  (let* ([cfg (build-cfg label-blocks)]
         [transpose-cfg (transpose cfg)]
         [_ (analyze-dataflow transpose-cfg (transfer name) (set) set-union)])
    uncovered-blocks))
  
(define (uncover-live p)
  (match p
    [(X86ProgramDefs info defs)
      (X86ProgramDefs info (map
                           (lambda (def)
                             (match def
                               [(Def name params rty info label-blocks)
                                (Def name params rty info (uncover-live-blocks label-blocks name))]))
                           defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (vector? locals-type var)
  (if (dict-has-key? locals-type var)
    (match (dict-ref locals-type var)
      [(list 'Vector _) #t]
      [_ #f])
    #f))

(define (get-label var)
  (match var
    [(Var x) x]
    [_ null]))

(define (build-interference-instr instr live-after g locals-type)
  (match instr
    [(Instr (or 'movq 'movzbq) `(,s ,d))
      (map (lambda (v) 
              (if (or (equal? v d) (equal? v s)) 
                (void) 
                (add-edge! g d v))) 
                (set->list live-after))
      g]
    [(or (Callq 'collect _) (IndirectCallq _ _) (TailJmp _ _))
      (let ([w (uncover-write instr)])
            (for* ([d w]
                   [v live-after])
                   (if (equal? d v) 
                     (void) 
                     (add-edge! g d v)))
        (define active-vectors (for/set ([v (set->list live-after)]
                                        #:when (and (not (null? (get-label v))) (vector? locals-type (get-label v)))) v))
        (for ([v active-vectors])
          (for ([w callee-saved])
            (add-edge! g v w)))
        g)]  
    [else (let ([w (uncover-write instr)])
                (for* ([d w]
                       [v live-after])
                       (if (equal? d v) 
                         (void) 
                         (add-edge! g d v)))
                g)])) 

(define (build-interference-block g block locals-type)
  (match block
    [(Block info instrs)
      (let* ([live-after (dict-ref info 'live-after)]
             [all-vertices (apply set-union live-after)])
              (for ([v (set->list all-vertices)])
                (add-vertex! g v))
              (for ([instr instrs] [l-aft live-after])
                (build-interference-instr instr l-aft g locals-type))
              (Block info instrs))]))

(define (build-interference p)
  (match p
    [(X86ProgramDefs info defs)
      (X86ProgramDefs info (map
                           (lambda (def)
                             (match def
                               [(Def name params rty info body)
                                (let* ([g (undirected-graph '())]
                                       [label-blocks (map (lambda (label-block)
                                                          (cons (car label-block) (build-interference-block g (cdr label-block) (dict-ref info 'locals-types))))
                                                          body)])
                                  (Def name params rty (dict-set info 'conflicts g) label-blocks))]))))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (color-pq graph queue v) queue)

(define unassignable-regs
  (list (cons (ByteReg 'al) -5)
        (cons (Reg 'rbp) -4)
        (cons (Reg 'r15) -3)
        (cons (Reg 'r11) -2)
        (cons (Reg 'rax) -1)
        (cons (Reg 'rbx)  0)
        (cons (Reg 'rcx)  1)
        (cons (Reg 'rdx)  2)
        (cons (Reg 'rsi)  3)
        (cons (Reg 'rdi)  4)
        (cons (Reg 'r8)   5)
        (cons (Reg 'r9)   6)
        (cons (Reg 'r10)  7)
        (cons (Reg 'r12)  8)
        (cons (Reg 'r13)  9)
        (cons (Reg 'r14) 10)))

(define color->reg
  (list (cons  0  (Reg 'rbx))
        (cons  1  (Reg 'rcx))
        (cons  2  (Reg 'rdx))
        (cons  3  (Reg 'rsi))
        (cons  4  (Reg 'rdi))
        (cons  5  (Reg 'r8))
        (cons  6  (Reg 'r9))
        (cons  7  (Reg 'r10))
        (cons  8  (Reg 'r12))
        (cons  9  (Reg 'r13))
        (cons  10 (Reg 'r14))))

(define (mex s)
  (define (helper s t)
    (if (set-member? s t)
        (helper s (+ t 1))
        t))
  (helper s 0))

; to account for registers that cannot be assigned, pushes back to -6 
(define (mex-heap-color s)
  (define (helper s t)
    (if (set-member? s t)
        (helper
         s
         (cond
           [(<= t -6) (- t 1)]
           [(eq? t 10) -6]
           [else (+ t 1)]))
        t))
  (helper s 0))

(define (update-mapping graph current-mapping v locals-type)
  (let 
    ([colors (for/set ([n (in-neighbors graph v)])
                    (if (dict-has-key? current-mapping n)
                        (dict-ref current-mapping n)
                        -1))])
      (dict-set current-mapping v
        (match v
          [(Var x) #:when (vector? locals-type x)
                    (mex-heap-color colors)]
          [_ (mex colors)]))))

(define (color-graph-recurse graph queue current-mapping locals-type)
  (if (= (pqueue-count queue) 0)
    current-mapping
    (let ([v (vector-ref (pqueue-pop! queue) 0)])
      (color-graph-recurse
        graph
        (color-pq graph queue v)
        (update-mapping graph current-mapping v locals-type)
        locals-type))))

(define (color-comparator v1 v2)
  (>= (vector-ref v1 1) (vector-ref v2 1))) ; node.second => priority

(define (color-graph graph locals-type)
  (let ([queue (make-pqueue color-comparator)])
    (for ([v (in-vertices graph)])
      (match v
        [(Reg reg) void]
        [_ (pqueue-push! queue (vector v (sequence-length (in-neighbors graph v))))]))
    (color-graph-recurse graph queue unassignable-regs locals-type)))

(define (get-mapping-from-color color)
  (if (dict-has-key? color->reg color)
      (dict-ref color->reg color)
      (if (>= color 0)
        (Deref 'rbp (* -8 (+ (- color (length color->reg)) 0)))
        (Deref 'r15 (* -8 (+ (- (+ color 6)) 0))))))

(define (allocate-registers-arg arg allocation locals-type)
  (match arg
    [(Var x) (get-mapping-from-color (dict-ref allocation arg))]
    [_ arg]))

(define (allocate-registers-instrs instrs allocation locals-type)
  (for/list ([instr instrs])
    (match instr
      [(Instr name args)
       (Instr name (for/list ([arg args])
                     (allocate-registers-arg arg allocation locals-type)))]
      [(IndirectCallq name arity)
       (IndirectCallq 
        (allocate-registers-arg name allocation locals-type) 
        arity)]
      [(TailJmp name arity)
       (TailJmp 
        (allocate-registers-arg name allocation locals-type) 
        arity)]
      [_ instr])))

(define (allocate-registers-blocks blocks allocation locals-type)
  (for/list ([block blocks])
    (match block
      [(cons label (Block blkinfo instrs))
       (cons label (Block blkinfo (allocate-registers-instrs instrs allocation locals-type)))])))

(define (allocate-registers p)
  (match p
    [(X86ProgramDefs info defs)
     (X86ProgramDefs
      info
      (map
       (lambda (def)
         (match def
           [(Def name params rty info blocks)
            (let*
                ([allocation (color-graph (dict-ref info 'conflicts) (dict-ref info 'locals-types))]
                 [info-stack
                  (dict-set
                    (dict-set 
                      info 
                      'num-root-spills
                      (max (- (+ 5 (apply min (map (lambda (x) (cdr x)) allocation)))) 0)) 
                    'num-stack-spills
                    (max (- (apply max (map (lambda (x) (cdr x)) allocation)) 11) 0))])
              (Def name params rty info-stack (allocate-registers-blocks blocks allocation (dict-ref info 'locals-types))))]
           ))
       defs))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define is-blk-tailjmp #f)

(define (patch-instructions-instrs instrs [name 'main])
  (match instrs
    ['() '()]
    [(cons (Instr 'movq (list arg1 arg2)) rest)
      #:when (equal? arg1 arg2) (patch-instructions-instrs rest)]
    [(cons (Instr x86-op (list arg1 arg2)) rest)
      (if (and (Deref? arg1) (Deref? arg2))
      (append 
        (list (Instr 'movq (list arg1 (Reg 'rax))) (Instr x86-op (list (Reg 'rax) arg2))) 
        (patch-instructions-instrs rest))
      (if (and (Imm? arg1) (> (Imm-value arg1) (expt 2 16)) (Deref? arg2))
        (append 
          (list (Instr 'movq (list arg1 (Reg 'rax))) (Instr x86-op (list (Reg 'rax) arg2))) 
          (patch-instructions-instrs rest))
        (cons (Instr x86-op (list arg1 arg2)) (patch-instructions-instrs rest))))]
    [(cons (Instr 'cmpq (list arg1 arg2)) rest)
      #:when (Imm? arg2) 
      (append
        (list (Instr 'movq (list arg2 (Reg 'rax))))
        (list (Instr 'cmpq (list arg1 (Reg 'rax))))
        (patch-instructions-instrs rest))]
    [(cons (Instr 'movzbq (list arg1 arg2)) rest)
     #:when (Deref? arg2)
     (append
      (list (Instr 'movzbq (list arg1 (Reg 'rax))))
      (list (Instr 'movq (list (Reg 'rax) arg2)))
      (patch-instructions-instrs rest))]
    [(cons (Instr 'leaq (list arg1 (Deref arg2 b))) rest)
     (append
      (list (Instr 'leaq (list arg1 (Reg 'rax))))
      (list (Instr 'movq (list (Reg 'rax) (Deref arg2 b))))
      (patch-instructions-instrs rest))]
    [(cons (TailJmp target arity) rest)
     (append 
      (list (Instr 'movq (list target (Reg 'rax))))
      (list (Jmp (func-conc-block-name name)))
      (patch-instructions-instrs rest)
     )]
    [(cons instr rest)
     (cons
      instr
      (patch-instructions-instrs rest))]))

(define (patch-instructions-blocks label-block-lst [name 'main])
  (for/list ([label-block label-block-lst])
    (match label-block
      [(cons label block)
       (match block
         [(Block blkinfo instrs)
          (cons label (Block blkinfo (patch-instructions-instrs instrs name)))])])))

(define (patch-instructions p)
  (match p
    [(X86ProgramDefs info defs)
      (X86ProgramDefs
        info
        (map
          (lambda (def)
            (set! is-blk-tailjmp #f)
            (match def
              [(Def name params rty info blocks)
                (Def 
                  name 
                  params 
                  rty 
                  (dict-set info 'tailjmp? is-blk-tailjmp) 
                  (patch-instructions-blocks blocks name))]))
          defs))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (prelude-and-conclusion p)
  (match p
    [(X86ProgramDefs info defs)
     (X86Program
      info
      (map
       (lambda (def)
         (match def
           [(Def name params rty info blocks)
            (Def name params rty info
              (append
                ;;;; PRELUDE ;;;;
                (list
                  (cons name
                    (Block '()
                      (list
                        (Instr 'pushq (list (Reg 'rbp)))
                        (Instr 'pushq (list (Reg 'rbx)))
                        (Instr 'pushq (list (Reg 'r12))) ;; callee
                        (Instr 'pushq (list (Reg 'r13)))
                        (Instr 'pushq (list (Reg 'r14))) 

                        (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                        (Instr 'subq (list (Imm (align (* 8 (add1 (dict-ref info 'num-stack-spills))) 16)) (Reg 'rsp)))

                        ;;; root stack
                        (if (eq? name 'main) 
                          (list
                            (Instr 'movq (list (Imm 16384) (Reg 'rdi)))
                            (Instr 'movq (list (Imm 16384) (Reg 'rsi)))
                            (Callq 'initialize 2)
                            (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
                          '())
                        
                        (Instr 'movq (list (Imm 0) (Deref 'r15 0)))
                        (Instr 'addq (list (Imm (align (* 8 (dict-ref info 'num-root-spills)) 16)) (Reg 'r15)))
                        (Jmp (func-start-block-name name))))))
                
                ;;;; BODY ;;;; 
                blocks
                
                ;;;; CONCLUSION ;;;;
                (list
                  (cons
                    (func-conc-block-name name)
                    (Block '()
                      (list
                        (Instr 'addq (list (Imm (align (* 8 (add1 (dict-ref info 'num-stack-spills))) 16)) (Reg 'rsp)))
                        (Instr 'popq (list (Reg 'r14)))
                        (Instr 'popq (list (Reg 'r13)))
                        (Instr 'popq (list (Reg 'r12)))
                        (Instr 'popq (list (Reg 'rbx)))
                        (Instr 'subq (list (Imm (align (* 8 (dict-ref info 'num-root-spills)) 16)) (Reg 'r15)))
                        (Instr 'popq (list (Reg 'rbp)))
                        (if (eq? (dict-ref info 'tailjmp) #t)
                          (IndirectJmp (Reg 'rax))
                          (Retq))))))))]))
        defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
    ("reveal functions" ,reveal-functions ,interp-Lfun-prime ,type-check-Lfun)
    ("limit functions" ,limit-functions ,interp-Lfun-prime ,type-check-Lfun)
    ("expose allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun)
    ("uncover get!" ,uncover-get!, interp-Lfun-prime ,type-check-Lfun)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime ,type-check-Lfun)
    ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
    ("instruction selection" ,select-instructions #f)
    ))