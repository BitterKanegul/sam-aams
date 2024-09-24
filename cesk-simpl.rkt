#lang racket
#|

State machine
<x, r, s ,k>             -> <v, r', s, k> where s(r(x)) = (v, r')
<(e0e1), r, s, k>           -> <e0, r, s, ar(e1, r, k)>
<v, r, s, ar(e, p',k)>      -> <e, r', s, fn(v, r, k)>
<v, r, s, fn((lx.e), p', k)> -> <e, r'[x -> a], s[a -> (v,r)], k> where a !∈ dom(s)

|#

;; Extending and looking up environment
(define (lookup-state x r s)
  (define res (hash-ref s (hash-ref r x)))
  (values (car res) (cdr res))
 )
(define (extend-env x v r r+ s)
  (define new-addr (gensym))
  (define r-upd (hash-set r x new-addr))
  (define s-upd (hash-set s new-addr (cons v r)))
  (values r-upd s-upd)
 )

(define (step state)
  (match state
    ;<x, r, s ,k>             -> <v, r', s, k> where s(r(x)) = (v, r')
    [`((ref ,(? symbol? x)) ,r ,s ,k)
      (define-values (v r+) (lookup-state x r s))
      `(,v ,r+ ,s ,k)
     ]
    ;<(e0e1), r, s, k>           -> <e0, r, s, ar(e1, r, k)>
    [`((app ,e0 ,e1) ,r ,s ,k)
      `(,e0 ,r ,s (ar ,e1 ,r ,k))
     ]
    ;(l (x) e1) e2) becomes function application
   ;[`((λ (,x) ,e) ,r ,s ,k)
   ;  (print "halt")
   ;  ]
    ;<v, r, s, ar(e, r',k)>      -> <e, r', s, fn(v, r, k)>
    [`(,v ,r ,s (ar ,e ,r+ ,k))
     `(,e ,r+ ,s (fnc ,v ,r ,k))
     ]
    ;<v, r, s, fn((lx.e), r', k)> -> <e, r'[x -> a], s[a -> (v,r)], k> where a !∈ dom(s)
    [`(,v ,r ,s (fnc (λ ,x ,e) ,r+ ,k))
     (define-values (r-upd s-upd) (extend-env x v r r+ s))
     `(,e ,r-upd ,s-upd ,k)
     ]
    ))
;; Start from (expr, {}, {}, mt)
(define (run-prog expr)
  (define r-init (hash))
  (define s-init (hash))
  (let loop ([i 1] [state `(,expr ,r-init ,s-init mt)])
   (displayln state)
   (let ([state1 (step state)])
   (let ([inp (read-line)])
     (when (not (equal? inp "q"))
       (loop (add1 i) state1))))))

(define test0 `(app (λ (x) (app (ref x) (ref x))) (λ (y) (ref y))))

(run-prog test0)  
