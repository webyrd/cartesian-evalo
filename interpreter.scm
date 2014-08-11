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

;; should seriously consider breaking the env into two lists and using
;; absento, to make this a lazy constraint
(define not-in-envo
  (lambda (x env)
    (conde
      ((== '() env))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest))))))

#|
;; pattern-matching version is easier to work with when taking the
;; Cartesian product of two calls to eval-expo

(define eval-expo
  (lambda (exp env val)
    (conde
      ((fresh (rator rand x body env2 a)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(closure ,x ,body ,env2))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env2) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (== `(closure ,x ,body ,env) val)
         (not-in-envo 'lambda env)))
      ((symbolo exp) (lookupo exp env val)))))
|#

(define eval-expo
  (lambda (exp env val)
    (matche exp
      [(,rator ,rand)
       (fresh (x body env2 a)
         (eval-expo rator env `(closure ,x ,body ,env2))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env2) val))]
      [(lambda (,x) ,body)
       (symbolo x)
       (== `(closure ,x ,body ,env) val)
       (not-in-envo 'lambda env)]
      [,x
       (symbolo x)
       (lookupo x env val)])))

;; relatively straight-forward version (non-recursive!)
;;
;; ??? how does this compare with small-step with intensional
;; interleaving?  I suspect small-step could do better/would be
;; cleaner
;;
;; may be that small step with interleaving is the best way to do
;; example-based program synthesis
(define eval-expo-double
  (lambda (exp1 env1 val1
           exp2 env2 val2)
    (matche (exp1 exp2)
      [((,rator1 ,rand1) (,rator2 ,rand2)) ; done
       ;; the trickiest one!  I suppose we could create some giant
       ;; eval-expo-6.  would want to generate that one!
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
       ;; yuck!  would be really nice to make not-in-envo a lazy
       ;; constraint!!  that way we can focus entirely on the
       ;; application case
       (not-in-envo 'lambda env2)
       ;; can safely call the single eval-expo here (in fact, I could
       ;; even call eval-expo-double for the first two recursions, or
       ;; even call an eval-expo-triple on all three sets of
       ;; expressions)
       (fresh (x1 body1 env^1 a1)
         (eval-expo rator1 env1 `(closure ,x1 ,body1 ,env^1))
         (eval-expo rand1 env1 a1)
         (eval-expo body1 `((,x1 . ,a1) . ,env^1) val1))]
      [((,rator1 ,rand1) ,x2) ; done
       (symbolo x2)
       ;; hmmm.  even if we have an eval-expo-triple, I guess we'd
       ;; have to combine it with lookupo for optimal results.  Unless
       ;; we can make lookupo a lazy constraint somehow.
       (lookupo x2 env2 val2)
       ;; can safely call the single eval-expo here (in fact, I could
       ;; even call eval-expo-double for the first two recursions, or
       ;; even call an eval-expo-triple on all three sets of
       ;; expressions)
       (fresh (x1 body1 env^1 a1)
         (eval-expo rator1 env1 `(closure ,x1 ,body1 ,env^1))
         (eval-expo rand1 env1 a1)
         (eval-expo body1 `((,x1 . ,a1) . ,env^1) val1))]
      ;;
      [((lambda (,x1) ,body1) (,rator2 ,rand2)) ; done
       (symbolo x1)
       (== `(closure ,x1 ,body1 ,env1) val1)
       ;; yuck!  would be really nice to make not-in-envo a lazy
       ;; constraint!!  that way we can focus entirely on the
       ;; application case
       (not-in-envo 'lambda env1)
       ;; can safely call the single eval-expo here (in fact, I could
       ;; even call eval-expo-double for the first two recursions, or
       ;; even call an eval-expo-triple on all three sets of
       ;; expressions)
       (fresh (x2 body2 env^2 a2)
         (eval-expo rator2 env2 `(closure ,x2 ,body2 ,env^2))
         (eval-expo rand2 env2 a2)
         (eval-expo body2 `((,x2 . ,a2) . ,env^2) val2))]
      [((lambda (,x1) ,body1) (lambda (,x2) ,body2)) ; done
       (symbolo x1) (symbolo x2)
       (== `(closure ,x1 ,body1 ,env1) val1)
       (== `(closure ,x2 ,body2 ,env2) val2)
       ;; if I don't change not-in-envo to use a constraint, I should
       ;; at least create a "double not-in-envo" relation
       (not-in-envo 'lambda env1)
       (not-in-envo 'lambda env2)]
      [((lambda (,x1) ,body1) ,x2) ; done
       (symbolo x1)
       (symbolo x2)
       (== `(closure ,x1 ,body1 ,env1) val1)
       ;; if I don't change not-in-envo to use a constraint, I should
       ;; at least create a not-in-envo/lookupo hybrid helper
       (not-in-envo 'lambda env1)
       (lookupo x2 env2 val2)]
      ;;
      [(,x1 (,rator2 ,rand2)) ; done
       (symbolo x1)
       ;; hmmm.  even if we have an eval-expo-triple, I guess we'd
       ;; have to combine it with lookupo for optimal results.  Unless
       ;; we can make lookupo a lazy constraint somehow.
       (lookupo x1 env1 val1)
       ;; can safely call the single eval-expo here (in fact, I could
       ;; even call eval-expo-double for the first two recursions, or
       ;; even call an eval-expo-triple on all three sets of
       ;; expressions)
       (fresh (x2 body2 env^2 a2)
         (eval-expo rator2 env2 `(closure ,x2 ,body2 ,env^2))
         (eval-expo rand2 env2 a2)
         (eval-expo body2 `((,x2 . ,a2) . ,env^2) val2))]
      [(,x1 (lambda (,x2) ,body2)) ; done
       (symbolo x1) (symbolo x2)
       (== `(closure ,x2 ,body2 ,env2) val2)
       ;; if I don't change not-in-envo to use a constraint, I should
       ;; at least create a not-in-envo/lookupo hybrid helper
       (not-in-envo 'lambda env2)
       (lookupo x1 env1 val1)]
      [(,x1 ,x2) ; done
       (symbolo x1) (symbolo x2)
       ;; should create a combined "double lookup" relation to cdr
       ;; down both envs at once
       (lookupo x1 env1 val1)
       (lookupo x2 env2 val2)])))

(test "interp-7"
  (run 5 (q)
    (fresh (e v)
      (eval-expo e '() v)
      (== `(,e -> ,v) q)))
  '((((lambda (_.0) _.1) -> (closure _.0 _.1 ())) (sym _.0))
    ((((lambda (_.0) _.0) (lambda (_.1) _.2))
      ->
      (closure _.1 _.2 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
      ->
      (closure _.1 _.2 ((_.0 closure _.3 _.4 ()))))
     (=/= ((_.0 lambda)))
     (sym _.0 _.1 _.3))
    ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1))
      ->
      (closure _.1 _.1 ()))
     (sym _.0 _.1))
    ((((lambda (_.0) (_.0 _.0))
       (lambda (_.1) (lambda (_.2) _.3)))
      ->
      (closure _.2 _.3 ((_.1 closure _.1 (lambda (_.2) _.3) ()))))
     (=/= ((_.1 lambda)))
     (sym _.0 _.1 _.2))))

(test "interp-8"
  (run 5 (q)
    (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
  '(((lambda (x) (lambda (y) x)) (lambda (z) z))
    ((lambda (x) (x (lambda (y) x))) (lambda (z) z))
    (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0))
    (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))
    ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0))))

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
