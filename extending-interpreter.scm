;(load "old-mk.scm")
(load "new-mk.scm")
(load "matche.scm")
(load "test-check.scm")

(define lookupo
  (lambda (x env t)
    (fresh (y v rest)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

(define not-in-envo
  (lambda (x env)
    (conde
      ((== '() env))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest))))))

(define proper-listo
  (lambda (exp env val)
    (conde
      ((== '() exp)
       (== '() val))
      ((fresh (a d v-a v-d)
         (== `(,a . ,d) exp)
         (== `(,v-a . ,v-d) val)
         (eval-expo a env v-a)
         (proper-listo d env v-d))))))

#|
(define eval-expo
  (lambda (exp env val)
    (conde
      ((fresh (v)
         (== `(quote ,v) exp)
         (not-in-envo 'quote env)
         (absento 'closure v)
         (== v val)))
      ((fresh (a*)
         (== `(list . ,a*) exp)
         (not-in-envo 'list env)
         (absento 'closure a*)
         (proper-listo a* env val)))
      ((symbolo exp) (lookupo exp env val))
      ((fresh (rator rand x body env^ a)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(closure ,x ,body ,env^))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env^) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (== `(closure ,x ,body ,env) val))))))
|#

(define eval-expo
  (lambda (exp env val)
    (matche exp
      [(quote ,v)
       (== v val)
       (absento 'closure v)
       (not-in-envo 'quote env)]
      [(list . ,a*)
       (absento 'closure a*)
       (not-in-envo 'list env)
       (proper-listo a* env val)]
      [,x
       (symbolo x)
       (lookupo x env val)]
      [(,rator ,rand)
       (fresh (x body env^ a)
         (eval-expo rator env `(closure ,x ,body ,env^))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env^) val))]
      [(lambda (,x) ,body)
       (symbolo x)
       (not-in-envo 'lambda env)
       (== `(closure ,x ,body ,env) val)])))

;; relatively straight-forward version (non-recursive!)
;;
;; ?? why is the "new" mk so much slower than the mk from the quines workshop?
;; (three times slower for twine-eval-expo-double-10)
;;
;; !! try calling helpers (and making recursive calls) that take
;; advantage of the interleaved evaluation
;;
;; ?? can I apply this approach to combinator synthesis in combinatory logic?
;;
;; ?? what is a good test for example-based program synthesis?  might
;; want to add cons, car, cdr, null?
;;
;; ?? can I automate this transformation?
(define eval-expo-double
  (lambda (exp1 env1 val1
           exp2 env2 val2)
    (matche (exp1 exp2)
      ;; quote
      [((quote ,v1) (quote ,v2)) ; done
       (== v1 val1) (== v2 val2)
       (absento 'closure v1)
       (absento 'closure v2)
       (not-in-envo 'quote env1)
       (not-in-envo 'quote env2)]
      [((quote ,v1) (list . ,a2*)) ; done
       (== v1 val1)
       (absento 'closure v1)
       (absento 'closure a2*)
       (not-in-envo 'quote env1)
       (not-in-envo 'list env2)
       (proper-listo a2* env2 val2)]
      [((quote ,v1) ,x2) ; done
       (symbolo x2)
       (== v1 val1)
       (absento 'closure v1)
       (not-in-envo 'quote env1)
       (lookupo x2 env2 val2)]
      [((quote ,v1) (,rator2 ,rand2)) ; done
       (== v1 val1)
       (absento 'closure v1)
       (not-in-envo 'quote env1)
       (fresh (x2 body2 env^2 a2)
         (eval-expo rator2 env2 `(closure ,x2 ,body2 ,env^2))
         (eval-expo rand2 env2 a2)
         (eval-expo body2 `((,x2 . ,a2) . ,env^2) val2))]
      [((quote ,v1) (lambda (,x2) ,body2)) ; done
       (== v1 val1)
       (== `(closure ,x2 ,body2 ,env2) val2)
       (symbolo x2)
       (absento 'closure v1)
       (not-in-envo 'quote env1)
       (not-in-envo 'lambda env2)] 
      ;; list
      [((list . ,a1*) (quote ,v2)) ; done
       (== v2 val2)
       (absento 'closure v2)
       (absento 'closure a1*)
       (not-in-envo 'quote env2)
       (not-in-envo 'list env1)
       (proper-listo a1* env1 val1)]
      [((list . ,a1*) (list . ,a2*)) ; done
       (absento 'closure a1*)
       (absento 'closure a2*)
       (not-in-envo 'list env1)
       (not-in-envo 'list env2)
       (proper-listo a1* env1 val1)
       (proper-listo a2* env2 val2)]
      [((list . ,a1*) ,x2) ; done
       (symbolo x2)
       (absento 'closure a1*)
       (not-in-envo 'list env1)
       (lookupo x2 env2 val2)
       (proper-listo a1* env1 val1)]
      [((list . ,a1*) (,rator2 ,rand2)) ; done
       (absento 'closure a1*)
       (not-in-envo 'list env1)
       (proper-listo a1* env1 val1)
       (fresh (x2 body2 env^2 a2)
         (eval-expo rator2 env2 `(closure ,x2 ,body2 ,env^2))
         (eval-expo rand2 env2 a2)
         (eval-expo body2 `((,x2 . ,a2) . ,env^2) val2))]
      [((list . ,a1*) (lambda (,x2) ,body2)) ; done
       (symbolo x2)
       (== `(closure ,x2 ,body2 ,env2) val2)
       (absento 'closure a1*)
       (not-in-envo 'list env1)
       (not-in-envo 'lambda env2)
       (proper-listo a1* env1 val1)]
      ;; x
      [(,x1 (quote ,v2)) ; done
       (== v2 val2)
       (symbolo x1)
       (absento 'closure v2)
       (not-in-envo 'quote env2)
       (lookupo x1 env1 val1)]
      [(,x1 (list . ,a2*)) ; done
       (symbolo x1)
       (absento 'closure a2*)
       (not-in-envo 'list env2)
       (lookupo x1 env1 val1)
       (proper-listo a2* env2 val2)]
      [(,x1 ,x2) ; done
       (symbolo x1) (symbolo x2)
       (lookupo x1 env1 val1)
       (lookupo x2 env2 val2)]
      [(,x1 (,rator2 ,rand2)) ; done
       (symbolo x1)
       (lookupo x1 env1 val1)
       (fresh (x2 body2 env^2 a2)
         (eval-expo rator2 env2 `(closure ,x2 ,body2 ,env^2))
         (eval-expo rand2 env2 a2)
         (eval-expo body2 `((,x2 . ,a2) . ,env^2) val2))]
      [(,x1 (lambda (,x2) ,body2)) ; done
       (symbolo x1) (symbolo x2)
       (== `(closure ,x2 ,body2 ,env2) val2)
       (lookupo x1 env1 val1)
       (not-in-envo 'lambda env2)]
      ;; application
      [((,rator1 ,rand1) (quote ,v2)) ; done
       (== v2 val2)
       (absento 'closure v2)
       (not-in-envo 'quote env2)
       (fresh (x1 body1 env^1 a1)
         (eval-expo rator1 env1 `(closure ,x1 ,body1 ,env^1))
         (eval-expo rand1 env1 a1)
         (eval-expo body1 `((,x1 . ,a1) . ,env^1) val1))]
      [((,rator1 ,rand1) (list . ,a2*)) ; done
       (absento 'closure a2*)
       (not-in-envo 'list env2)
       (proper-listo a2* env2 val2)
       (fresh (x1 body1 env^1 a1)
         (eval-expo rator1 env1 `(closure ,x1 ,body1 ,env^1))
         (eval-expo rand1 env1 a1)
         (eval-expo body1 `((,x1 . ,a1) . ,env^1) val1))]
      [((,rator1 ,rand1) ,x2) ; done
       (symbolo x2)
       (lookupo x2 env2 val2)
       (fresh (x1 body1 env^1 a1)
         (eval-expo rator1 env1 `(closure ,x1 ,body1 ,env^1))
         (eval-expo rand1 env1 a1)
         (eval-expo body1 `((,x1 . ,a1) . ,env^1) val1))]
      [((,rator1 ,rand1) (,rator2 ,rand2)) ; done
       (fresh (x1 body1 env^1 a1)
         (eval-expo rator1 env1 `(closure ,x1 ,body1 ,env^1))
         (eval-expo rand1 env1 a1)
         (eval-expo body1 `((,x1 . ,a1) . ,env^1) val1))
       (fresh (x2 body2 env^2 a2)
         (eval-expo rator2 env2 `(closure ,x2 ,body2 ,env^2))
         (eval-expo rand2 env2 a2)
         (eval-expo body2 `((,x2 . ,a2) . ,env^2) val2))]
      [((,rator1 ,rand1) (lambda (,x2) ,body2)) ; done
       (symbolo x2)
       (== `(closure ,x2 ,body2 ,env2) val2)
       (not-in-envo 'lambda env2)
       (fresh (x1 body1 env^1 a1)
         (eval-expo rator1 env1 `(closure ,x1 ,body1 ,env^1))
         (eval-expo rand1 env1 a1)
         (eval-expo body1 `((,x1 . ,a1) . ,env^1) val1))]
      ;; lambda
      [((lambda (,x1) ,body1) (quote ,v2)) ; done
       (== v2 val2)
       (== `(closure ,x1 ,body1 ,env1) val1)
       (symbolo x1)
       (absento 'closure v2)
       (not-in-envo 'lambda env1)
       (not-in-envo 'quote env2)]
      [((lambda (,x1) ,body1) (list . ,a2*)) ; done
       (== `(closure ,x1 ,body1 ,env1) val1)
       (symbolo x1)
       (absento 'closure a2*)
       (not-in-envo 'lambda env1)
       (not-in-envo 'list env2)
       (proper-listo a2* env2 val2)]
      [((lambda (,x1) ,body1) ,x2) ; done
       (== `(closure ,x1 ,body1 ,env1) val1)
       (symbolo x1) (symbolo x2)
       (not-in-envo 'lambda env1)
       (lookupo x2 env2 val2)]
      [((lambda (,x1) ,body1) (,rator2 ,rand2)) ; done
       (== `(closure ,x1 ,body1 ,env1) val1)
       (symbolo x1)
       (not-in-envo 'lambda env1)       
       (fresh (x2 body2 env^2 a2)
         (eval-expo rator2 env2 `(closure ,x2 ,body2 ,env^2))
         (eval-expo rand2 env2 a2)
         (eval-expo body2 `((,x2 . ,a2) . ,env^2) val2))]
      [((lambda (,x1) ,body1) (lambda (,x2) ,body2)) ; done
       (symbolo x1) (symbolo x2)
       (== `(closure ,x1 ,body1 ,env1) val1)
       (== `(closure ,x2 ,body2 ,env2) val2)
       (not-in-envo 'lambda env1)
       (not-in-envo 'lambda env2)])))

(test "eval-expo-1"
  (run* (q) (eval-expo '(quote 5) '() q))
  '(5))

(test "extend-3"
  (run* (q) (eval-expo '((lambda (quote) (quote (lambda (x) x))) (lambda (y) y)) '() q))
  '((closure x x ((quote . (closure y y ()))))))

(test "quine-1"
  (time (run 1 (q) (eval-expo q '() q)))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
      '(lambda (_.0) (list _.0 (list 'quote _.0))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "quine-10"
  (time (length (run 10 (q) (eval-expo q '() q))))
  10)

(test "twine-1"
  (time (run 1 (x)
          (fresh (p q)
            (=/= p q)
            (eval-expo p '() q)
            (eval-expo q '() p)
            (== (list p q) x))))
  '((('((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
        '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))
      ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
       '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "twine-5"
  (time (run 5 (x)
          (fresh (p q)
            (=/= p q)
            (eval-expo p '() q)
            (eval-expo q '() p)
            (== (list p q) x))))
  '((('((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))) '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))) ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))) '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (('((lambda (_.0) (list 'quote (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))) '(lambda (_.0) (list 'quote (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))) ((lambda (_.0) (list 'quote (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))) '(lambda (_.0) (list 'quote (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (sym _.0 _.1) (absento (closure _.2))) (((list '(lambda (_.0) (list 'list _.0 (list 'quote (list 'quote _.0)))) '''(lambda (_.0) (list 'list _.0 (list 'quote (list 'quote _.0))))) ((lambda (_.0) (list 'list _.0 (list 'quote (list 'quote _.0)))) ''(lambda (_.0) (list 'list _.0 (list 'quote (list 'quote _.0)))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (('((lambda (_.0) (list ((lambda (_.1) 'quote) '_.2) (list _.0 (list 'quote _.0)))) '(lambda (_.0) (list ((lambda (_.1) 'quote) '_.2) (list _.0 (list 'quote _.0))))) ((lambda (_.0) (list ((lambda (_.1) 'quote) '_.2) (list _.0 (list 'quote _.0)))) '(lambda (_.0) (list ((lambda (_.1) 'quote) '_.2) (list _.0 (list 'quote _.0)))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 quote))) (sym _.0 _.1) (absento (closure _.2))) (('((lambda (_.0) (list 'quote (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))) '(lambda (_.0) (list 'quote (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))))) ((lambda (_.0) (list 'quote (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))) '(lambda (_.0) (list 'quote (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 quote))) (sym _.0 _.1) (absento (closure _.2)))))

(test "twine-10"
  (time (length (run 10 (x)
                  (fresh (p q)
                    (=/= p q)
                    (eval-expo p '() q)
                    (eval-expo q '() p)
                    (== (list p q) x)))))
  10)

(test "twine-eval-expo-double-1"
  (time (run 1 (x)
          (fresh (p q)
            (=/= p q)
            (eval-expo-double p '() q
                              q '() p)
            (== (list p q) x))))
  '((('((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
        '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))
      ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
       '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
     (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
     (sym _.0))))

(test "twine-eval-expo-double-10"
  (time (length (run 10 (x)
                  (fresh (p q)
                    (=/= p q)
                    (eval-expo-double p '() q
                                      q '() p)
                    (== (list p q) x)))))
  10)



(test "eval-expo-double-1"
  (run* (q)
    (fresh (v1 v2)
      (eval-expo-double '(lambda (x) x) '() v1
                        '(lambda (y) y) '() v2)
      (== (list v1 v2) q)))
  '(((closure x x ())
     (closure y y ()))))

(test "eval-expo-double-2a"
  (run* (q)
    (fresh (e2 v2)
      (eval-expo-double '(lambda (x) x) '() 'impossible
                        e2 '() v2)))
  '())

(test "eval-expo-double-2b"
  (run* (q)
    (fresh (e1 v1)
      (eval-expo-double e1 '() v1
                        '(lambda (y) y) '() 'impossible)))
  '())

(test "eval-expo-tricky-1a"
  (run* (q)
    (fresh (e2 v2)
      (eval-expo '(lambda (x) x) '() 'impossible)
      (eval-expo e2 '() v2)))
  '())

#!eof

;; diverges, as expected, although eval-expo-double-2b fails finitely
;;
;; in this case, at least, we benefit from combining the two calls to
;; eval-expo and interleaving evaluation.
(test "eval-expo-tricky-1b"
  (run 1 (q)
    (fresh (e1 v1)
      (eval-expo e1 '() v1)
      (eval-expo '(lambda (y) y) '() 'impossible)))
  '())
