#lang racket

#|
Implementing AAM in racket.
https://arxiv.org/pdf/1007.4446

CEK Machine states:
<x, r ,k>                -> <v, r', k> where r(x) = (v, r')
<(e0e1), r, k>           -> <e0, r, ar(e1, r, k)>
<v, r, ar(e, p',k)>      -> <e, r', fn(v, r, k)>
<v, r, fn((lx.e), p', k)> -> <e, r'[x ->  (v,r)], k>

x ->  x ∈ Var,  a set of identifiers.
e -> e ∈ Exp ::= x | (ee) | (λx.e)


Defining expressions:
E ::= [ ] | (Ee) | (vE).

An expression is either a value or uniquely decomposable into an
evaluation context and redex. The standard reduction machine is:

However, this machine does not shed much light on a realistic implementation.
At each step, the machine traverses the entire source of the program looking for a redex.
When found, the redex is reduced and the contractum is plugged back in the hole, then the process is repeated.

Abstract machines such as the CEK machine, which are derivable from standard reduction machines,
offer an extensionally equivalent but more realistic model of evaluation that is amenable
to efficient implementation.
The CEK is environment-based; it uses environments and closures to model substitution.
It represents evaluation contexts as continuations, an inductive data structure that models contexts in an inside-out manner.
The key idea of machines such as the CEK is that the whole program need not be traversed
to find the next redex, consequently the machine integrates the process of plugging a contractum into a context and finding the next
redex.

(My interpretation: CEK has a stack that allows it to implicitly figure out the next "active" part of the program)


States of the CEK machine [12] consist of a control string (an expression), an environment that closes the control string, and a
continuation:
ς ∈ Σ = Exp × Env × Kont
v ∈ Val ::= (λx.e)
ρ ∈ Env = Var →fin Val × Env
κ ∈ Kont ::= mt | ar(e, ρ, κ) | fn(v, ρ, κ).

States are identified up to consistent renaming of bound variables
Environments are finite maps from variables to closures.

Environment extension is written ρ[x → (v, ρ′)].

Evaluation contexts E are represented (inside-out) by continuations as follows: [ ] is represented by mt;
E[([ ]e)] is represented by ar(e', ρ, κ) where ρ closes e to represent e and κ represents E;
E[(v[ ])] is represented by fn(v, ρ, κ) where ρ closes v to represent v and κ represents E.



The transition function for the CEK machine is defined in Figure 1 (we follow the textbook treatment of the CEK machine [11,
page 102]).
The initial machine state for a closed expression e is given by the inj function:
inj CEK (e) = <e, ∅, mt>.


Typically, an evaluation function is defined as a partial function from closed expressions to answers:
eval′ CEK (e) = (v, ρ) if inj(e) |-→→CEK <v,ρ,mt>


This gives an extensional view of the machine, which is useful, e.g.,
to prove correctness with respect to a canonical evaluation function
such as one defined by standard reduction or compositional valuation. 

However for the purposes of program analysis, we are concerned more with the intensional aspects of the machine. As such,
we define the meaning of a program as the (possibly infinite) set of
reachable machine states:
eval CEK (e) = {ς | inj(e) |−→→CEK ς}.


Deciding membership in the set of reachable machine states is not possible due to the halting problem.
The goal of abstract interpretation, then, is to construct a function, aval /CEK\, that is a
sound and computable approximation to the eval_CEK function.

We can do this by constructing a machine that is similar in structure to the CEK machine: it is defined by an abstract state transition
relation (|−→ /CEK\) ⊆ Σˆ × Σˆ, which operates over abstract states,
Σˆ, which approximate the states of the CEK machine, and an abstraction map α : Σ → Σˆ that maps concrete machine states into
abstract machine states



Ok, we first implement the CEK machine here in racket.
|#



;; State space definitions
(struct state {control        ; exp
               environment    ; env
               continuation}) ; kont

; ρ : env = symbol -> addr
; value = x, (e e) (lambda x e)
; κ : kont ::= Mt, apply_arg, apply_func


;;CEK Machine states:

;;<x, r ,k>                -> <v, r', k> where r(x) = (v, r')
;;<(e0e1), r, k>           -> <e0, r, ar(e1, r, k)>
;;<v, r, ar(e, r',k)>      -> <e, r', fn(v, r, k)>
;;<v, r, fn((lx.e), p', k)> -> <e, r'[x ->  (v,r)], k>


; Define the Expression datatype
(struct literal (value) #:transparent)
(struct Var (name) #:transparent)
(struct λ (param body) #:transparent)

; Define the Environment
; Define the Environment as a hash map
(define (make-env) (make-hash))

(define (extend-env var val env)
  (hash-set! env var val)
  env)

(define (lookup-env var env)
  (hash-ref env var
            (lambda ()(error 'lookup-env "Unbound Var: ~a" var))))


; Continuations
(struct Mt ())
(struct Ar (exp env k))
(struct Fn (val k))

; run function
(define (run exp env k)
  (match exp
    [(literal v) (continue k v)]
    ;;<x, r ,k>        -> <v, r', k> where r(x) = (v, r')
    [(Var x) (continue k (lookup-env x env))]
    [(λ p b) (continue k (closure p b env))]
    ;;<(e0e1), r, k>   -> <e0, r, ar(e1, r, k)>
    [(list e1 e2) 
     (run e1 env (Ar e2 env k))]
    [_ (error 'run "Invalid Exp: ~a" exp)]))

; continue function
(define (continue k v)
  (match k
    [(Mt) v]
    ;;<v, r, ar(e, r',k)> -> <e, r', fn(v, r, k)>
    [(Ar e env k)
     (run e env (Fn v k))]
    ;;<v, r, fn((lx.e), p', k)> -> <e, r'[x ->  (v,r)], k>
    [(Fn (closure p b env) k)
     (run b (extend-env p v env) k)]))

; Closure structure
(struct closure (param body env))

; Main evaluation function
(define (cek exp)
  (run exp (make-env) (Mt)))

; Example 
(define test-exp
  (list
   (λ 'x (Var 'x))
   (literal 5)))

(displayln (cek test-exp))


(define complex-exp
  (list
   (λ 'f
     (list (Var 'f)
           (literal 3)))
   (λ 'x
     (list
      (list
       (λ 'y
         (λ 'z
           (list
            (list (Var 'y) (Var 'z))
            (Var 'x))))
       (λ 'a (λ 'b (Var 'a))))
      (literal 4)))))

(displayln (cek complex-exp))









