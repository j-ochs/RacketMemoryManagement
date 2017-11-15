#lang plai-typed
(print-only-errors #t)

#|-------------------------------------------------------------
Jacob Ochs
Memory Management & Garbage Collection
CS-105: Programming Languages
November 13, 2017

Minor conceptual help given to:
    Jason Campbell
Minor conceptual help received from:
    James Solum, Jason Campbell
---------------------------------------------------------------|#


;; type for surface representations
(define-type ExprS
  [numS (n : number)]
  [varS (s : symbol)]
  [appS (fun : ExprS) (arg : ExprS)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [lamS (param : symbol) (body : ExprS)]
  [withS (id : symbol) (binding-expr : ExprS) (bound-body : ExprS)]
  [boxS (arg : ExprS)]
  [unboxS (arg : ExprS)]
  [setboxS (b : ExprS) (v : ExprS)]
  [setS (v : symbol) (a : ExprS)]
  [seqS (e1 : ExprS) (e2 : ExprS)]
  [if0S (test : ExprS) (then : ExprS) (else : ExprS)]
  [recS (name : symbol) (f : ExprS) (b : ExprS)]
  [firstS (e : ExprS)]
  [restS (e : ExprS)]
  [consS (f : ExprS) (r : ExprS)]
  )

;; type for core representations
(define-type ExprC
  [numC (n : number)]
  [varC (s : symbol)]
  [appC (fun : ExprC) (arg : ExprC)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [lamC (param : symbol) (body : ExprC)]
  [boxC (arg : ExprC)]
  [unboxC (arg : ExprC)]
  [setboxC (b : ExprC) (v : ExprC)]
  [setC (v : symbol) (a : ExprC)]
  [seqC (e1 : ExprC) (e2 : ExprC)]
  [if0C (test : ExprC) (then : ExprC) (else : ExprC)]
  [consC (f : ExprC) (r : ExprC)]
  [firstC (v : ExprC)]
  [restC (v : ExprC)]
  )

;; types for values
(define-type Value
  [numV (n : number)]
  [closV (param : symbol) (body : ExprC) (env : Env)]
  [boxV (l : Location)]
  [consV (f : ExprC) (r : ExprC)])



;; type for returning both Value and Store from interp
(define-type Result
  [v*s (v : Value)])

;; types and defs for Environments and Stores
(define-type-alias Location number)

(define-type Binding [bind (name : symbol) (loc : Location)])
(define-type-alias Env (listof Binding))
(define mt-Env empty)
(define extend-env cons)

(define-type Storage [cell (loc : Location) (val : Value)])
(define MEMORY_SIZE 20)
(define placeholder 0)
(define Store (make-vector MEMORY_SIZE (numV placeholder))) ;; Store vector
(define free-list (make-vector MEMORY_SIZE (numV placeholder))) ;; free-list with alloc mappings to Store
(define mt-Sto empty)
(define full-Sto (make-vector MEMORY_SIZE (numV 99)))
(define test-env (list (bind 'a 9) (bind 'b 2) (bind 'c 5)))
(define full-env (list (bind 'a 1) (bind 'b 3) (bind 'c 4)
                       (bind 'a 19) (bind 'b 12) (bind 'c 11)
                       (bind 'a 0) (bind 'b 18) (bind 'c 17)
                       (bind 'a 14) (bind 'b 13) (bind 'c 10)
                       (bind 'a 15) (bind 'b 16) (bind 'c 6)
                       (bind 'a 9) (bind 'b 2) (bind 'c 5)
                       (bind 'a 7) (bind 'b 8)))



;; displays the Store and Free-list vectors for user reference
;; 0 == free memory, 1 == allocated memory (in the free-list)
(define (show-mem) : void
  (begin (display "STORE: ")
         (display Store)
         (display "FREE-LIST: ")
         (display free-list)))



;; executes all the computation for new-loc, using a scoped index var
(define (alloc-mem [num : number] [i : number] [env : Env]) : number
  (cond [(and (= num 1) (< i MEMORY_SIZE))
         (if (not (= (numV-n (vector-ref free-list i)) 1))
               (begin
                 (vector-set! free-list i (numV 1))
                 i)
             (begin
               (display " memory allocated at i=")
               (display i)
               (alloc-mem num (add1 i) env)
               i))]
        [(and (= num 2) (< i MEMORY_SIZE))
         (if (and (not (= (numV-n (vector-ref free-list i)) 1))
                  (not (= (numV-n (vector-ref free-list (add1 i))) 1)))
           (begin
             (vector-set! free-list i (numV 1))
             (vector-set! free-list (add1 i) (numV 1))
             i)
           (begin
               (display i)
               (alloc-mem num (add1 i) env)
               i))]
        [(>= i MEMORY_SIZE) (garbage-collect env)] ;;trigger GC
        [else (begin (display num)
                (error 'new-loc "invalid: must allocate either 1 or 2 memory locations"))]))



;; inserts a value into the store at the speciried location
;; and marks this space as allocated in our free-list
(define (override-store [val : Value] [loc : Location] [env : Env]) : number
  (cond [(consV? val) (begin
                        (vector-set! Store loc val)
                        (alloc-mem 2 loc env))]
        [else (begin
                (vector-set! Store loc val)
                (alloc-mem 1 loc env))]))



;; ############################ NEW-LOC / FREE-LOC ##############################

;; "allocate" unique "memory" locations for values in our free-list
;; RUNTIME COMPLEXITY for new-loc is <= O(n), where n = MEMORY_SIZE,
;; because the length of the vector is the maximum value over which
;; we will recurse. Otherwise, it will return an error
(define (new-loc [loc : number] [env : Env]) : number
  (let ([i 0])
    (alloc-mem loc i env)))
(test/exn (new-loc 3 mt-Env) "invalid: must allocate either 1 or 2 memory locations")



;; "free" unique "memory" locations for values in our free-list
;; RUNTIME COMPLEXITY for free-loc is = O(1), due to the constant-time
;; access of vector-set! on any arbitrary element in the vector
(define (free-loc [loc : Location] [num : number]) : void
  (cond [(or (or (< loc 0) (>= loc MEMORY_SIZE))
             (and (= (sub1 MEMORY_SIZE) loc) (= num 2))) (error 'free-loc "memory request out of range")]
        [(= num 1) (vector-set! free-list loc (numV 0))]
        [(= num 2) (begin (vector-set! free-list loc (numV 0))
                          (vector-set! free-list (add1 loc) (numV 0)))]
        [else (error 'free-loc "invalid arg: 2nd arg must be 1 or 2")]))

;; free-loc tests
(test/exn (free-loc 55 1) "memory request out of range")
(test/exn (free-loc 5 5) "invalid arg: 2nd arg must be 1 or 2")


;; ############################ GARBAGE COLLECTION FUNCS ##############################

;; reclaims spaces in the Store which correspond to the updated free-list
(define (collect-store [env : Env] [i : number]) : void
  (cond [(>= i MEMORY_SIZE) (display "GC finished")]
        [(= (numV-n (vector-ref free-list i)) placeholder)
         (begin
           (display " Store collected at i=")
           (display i)
           (vector-set! Store i (numV 0))
           (collect-store env (add1 i)))]
        [else (collect-store env (add1 i))]))
;(test (collect-store test-env MEMORY_SIZE) (display "GC finished"))



;; reclaims spaces in the free-list which correspond to the environment
(define (collect-free-list [env : Env]) : void
  (let ([i 0])
    (cond [(empty? env) (collect-store env i)] ;; collect Store values
          [else (begin
                  (vector-set! free-list (bind-loc (first env)) (numV 1))
                  (collect-free-list (rest env)))])))



;; collects unused memory in our Store and free-list as it corresponds
;; to the current memory use in the environment (ignoring fragmentation)
;; RUNTIME COMPlEXITY is = O(n), because the max iteration through
;; the free-list & the Store is 2n which is still O(n), where n = MEMORY_SIZE
(define (garbage-collect [env : Env]) : number
  (cond [(= MEMORY_SIZE (length env)) (error 'garbage-collect "out of memory: Env is full")]
        [else (begin
                (set! free-list (make-vector MEMORY_SIZE (numV placeholder)))
                (collect-free-list env)
                0)]))

(test/exn (garbage-collect full-env) "out of memory: Env is full")



;; ############################# PARSE ###############################
(define (parse [s : s-expression]) : ExprS
  ;; parse S-expressions into a surface representation that can be programmatically manipulated
  (cond [(s-exp-number? s) (numS (s-exp->number s))]
        [(s-exp-symbol? s) (varS (s-exp->symbol s))]
        [(s-exp-list? s)
         (let ([sl (s-exp->list s)])
           (cond
             [(s-exp-list? (first sl))
              (appS (parse (first sl)) (parse (second sl)))]
             [else
              (case (s-exp->symbol (first sl))
                [(+) (plusS (parse (second sl)) (parse (third sl)))]
                [(-) (if (= (length sl) 3)
                         (bminusS (parse (second sl)) (parse (third sl)))
                         (uminusS (parse (second sl))))]
                [(*) (multS (parse (second sl)) (parse (third sl)))]
                [(lambda) (lamS (s-exp->symbol (second sl))
                                (parse (third sl)))]
                [(with) (let ([bpair (s-exp->list (second sl))])
                          (withS (s-exp->symbol (first bpair))
                                 (parse (second bpair))
                                 (parse (third sl))))]
                [(box) (boxS (parse (second sl)))]
                [(unbox) (unboxS (parse (second sl)))]
                [(set-box!) (setboxS (parse (second sl)) (parse (third sl)))]
                [(begin) (seqS (parse (second sl)) (parse (third sl)))]
                [(set!) (setS (s-exp->symbol (second sl))
                              (parse (third sl)))]
                [(if0) (if0S (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
                [(rec) (recS (s-exp->symbol (second sl))
                             (parse (third sl))
                             (parse (fourth sl)))]
                [(cons) (consS (parse (second sl)) (parse (third sl)))]
                [(first) (firstS (parse (second sl)))]
                [(rest) (restS (parse (second sl)))]
                [else (appS (parse (first sl))
                            (parse (second sl)))])]))]
        [else (error 'parse "invalid input")]
        ))

;; parse tests
(test (parse '4) (numS 4))
(test (parse '(* (+ 3 4) (* 2 (+ 1 2))))
      (multS (plusS (numS 3) (numS 4))
             (multS (numS 2) (plusS (numS 1) (numS 2)))))
(test (parse '(- 8)) (uminusS (numS 8)))
(test (parse '(- (+ 3 4))) (uminusS (plusS (numS 3) (numS 4))))
(test (parse '(lambda x (+ x x))) (lamS 'x (plusS (varS 'x) (varS 'x))))
(test (parse '(with (x 3) (+ x x))) (withS 'x (numS 3) (plusS (varS 'x) (varS 'x))))
(test (parse '(with (b (box 0)) (set! b (begin (set-box! b 10)
                                               (unbox b)))))
      (withS 'b (boxS (numS 0)) (setS 'b (seqS (setboxS (varS 'b) (numS 10))
                                               (unboxS (varS 'b))))))


;; ############################# DESUGAR ###############################
(define (desugar [as : ExprS]) : ExprC
  ;; transform programs in surface syntax representation into core representation
  (type-case ExprS as
    [numS (n) (numC n)]
    [varS (s) (varC s)]
    [appS (f a) (appC (desugar f) (desugar a))]
    [plusS (l r) (plusC (desugar l) (desugar r))]
    [bminusS (l r) (plusC (desugar l)
                          (multC (numC -1) (desugar r)))]
    [multS (l r) (multC (desugar l) (desugar r))]
    [uminusS (e) (multC (numC -1) (desugar e))]
    [lamS (p b) (lamC p (desugar b))]
    [withS (id be bb) (appC (lamC id (desugar bb))
                            (desugar be))]
    [boxS (a) (boxC (desugar a))]
    [unboxS (a) (unboxC (desugar a))]
    [setboxS (b v) (setboxC (desugar b) (desugar v))]
    [setS (v a) (setC v (desugar a))]
    [seqS (e1 e2) (seqC (desugar e1) (desugar e2))]
    [if0S (t y n) (if0C (desugar t) (desugar y) (desugar n))]
    [recS (n f b) (desugar (withS n (numS -1) (seqS (setS n f) b)))]
    [firstS (e) (firstC (desugar e))]
    [restS (e) (restC (desugar e))]
    [consS (f r) (consC (desugar f) (desugar r))]
    ))

;;desugar tests
(test (desugar (numS 3)) (numC 3))
(test (desugar (multS (numS 2) (numS 3)))
      (multC (numC 2) (numC 3)))
(test (desugar (uminusS (numS 8))) (multC (numC -1) (numC 8)))
(test (desugar (uminusS (plusS (numS 3) (numS 4))))
      (multC (numC -1) (plusC (numC 3) (numC 4))))
(test (desugar (parse '(with (b (box 0)) (set! b (begin (set-box! b 10)
                                                        (unbox b))))))
      (appC (lamC 'b (setC 'b (seqC (setboxC (varC 'b) (numC 10))
                                    (unboxC (varC 'b)))))
            (boxC (numC 0))))



(define (lookup-binding [id : symbol] [env : Env]) : Location
  ;; retrieve the location to which this identifier is bound
  (cond [(empty? env) (error 'lookup-binding "unbound id")]
        [(symbol=? id (bind-name (first env))) (bind-loc (first env))]
        [else (lookup-binding id (rest env))]))


(define (fetch [loc : Location]) : Value
  ;; retrieve the value stored in the given location
  (cond [(or (< loc 0) (> loc MEMORY_SIZE)) (error 'fetch "memory request out of range")]
        [else (vector-ref Store loc)]))
;; fetch tests
(test/exn (fetch 90) "memory request out of range")


;; ############################ INTERP ##############################
(define (interp [a : ExprC] [env : Env]) : Result
  (type-case ExprC a
    [numC (n) (v*s (numV n))]
    [varC (s) (v*s (fetch (lookup-binding s env)))]
    [appC (f a) (type-case Result (interp f env)
                  [v*s (v-f)
                       (type-case Result (interp a env)
                         [v*s (v-a)
                              (let ([where (new-loc 1 env)])
                                (begin (override-store v-a where env)
                                        (interp (closV-body v-f)
                                                (extend-env (bind (closV-param v-f) where) (closV-env v-f))
                                        )))])])]
    [plusC (l r) (type-case Result (interp l env)
                   [v*s (v-l)
                        (type-case Result (interp r env)
                          [v*s (v-r)
                               (v*s (num+ v-l v-r))])])]
    [multC (l r) (type-case Result (interp l env)
                   [v*s (v-l)
                        (type-case Result (interp r env)
                          [v*s (v-r)
                               (v*s (num* v-l v-r))])])]
    [lamC (p b) (v*s (closV p b env))]
    [boxC (a) (type-case Result (interp a env)
                [v*s (v-a)
                     (let ([where (new-loc 1 env)])
                       (begin (override-store v-a where env)
                              (v*s (boxV where))
                            ))])]
    [unboxC (a) (type-case Result (interp a env)
                  [v*s (v-a)
                       (v*s (fetch (boxV-l v-a)))])]
    [setboxC (b a) (type-case Result (interp b env)
                     [v*s (v-b)
                          (type-case Result (interp a env)
                            [v*s (v-a)
                                 (begin (override-store v-a (boxV-l v-b) env)
                                 (v*s v-a
                                      ))])])]
    [setC (v a) (type-case Result (interp a env)
                  [v*s (v-a)
                       (let ([where (lookup-binding v env)])
                         (v*s v-a
                              ))])]
    [seqC (e1 e2) (type-case Result (interp e1 env)
                    [v*s (v-e1)
                         (interp e2 env)])]
    [if0C (t y n) (type-case Result (interp t env)
                    [v*s (vt)
                         (if (and (numV? vt) (zero? (numV-n vt)))
                             (interp n env)
                             (interp y env))])]
    [consC (f r) (v*s (consV f r))]
    [firstC (v) (v*s (consV v v))]
    [restC (v) (v*s (consV v v))]
    ))


(define (num+ [l : Value] [r : Value]) : Value
  (cond [(and (numV? l) (numV? r))
         (numV (+ (numV-n l) (numV-n r)))]
        [else (error 'num+ "bad arg")]))
(define (num* [l : Value] [r : Value]) : Value
  (cond [(and (numV? l) (numV? r))
         (numV (* (numV-n l) (numV-n r)))]
        [else (error 'num* "bad arg")]))

;; ############################# ASW ###############################
(define (asw [s : s-expression]) : Value
  ;; A Swell Wrapper function to interp expressions
  ;;  w/out typing interp, desugar and parse and our-functions
  (v*s-v (interp (desugar (parse s)) mt-Env)))

;; asw tests
(test (asw '(* (+ 3 4) (* 2 3))) (numV 42))
(test (asw '(- 7 2)) (numV 5))
(test (asw '(+ 3 (- 1))) (numV 2))
#|(test (asw '(with (x 7)
                  (begin (set! x 0)
                         (+ x 1))))
      (numV 1))|#
(test (interp (plusC (numC 1) (numC 2)) mt-Env)
      (v*s (numV 3)))

