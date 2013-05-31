#lang cKanren

(require cKanren/miniKanren)
(require cKanren/neq)
(require cKanren/absento)
(require cKanren/template)

(provide (all-defined-out))

;;; Untyped lambda-calculus rules from p.72 of Pierce's 'Types and Programming Languages'.
;;;
;;; This approach doesn't to work in general.  For example,
;;; reducing ((lambda (_.0) _.1) (lambda (_.2) _.3)) yields (lambda (_.4) _.5)
;;;
;;; Would it be better if templateo took a list of variables to copy, and only copied those?
;;; (run* (q ) (fresh (x y) (templateo `(,x) `(lambda (,x) ,y) q))
;;; would associate q with `(lambda (,x^) ,y^), where y^ = y, but with any occurrence of x in y lazily replaced with x^.
;;; Does this make sense?  Would this solve the problem above?  Would need a way of expressing that lazy substitution constraint.

(define valueo
  (lambda (t)
    (fresh (x t^)
      (== `(lambda (,x) ,t^) t)
      (symbolo x))))

(define not-valueo
  (lambda (t)
    (fresh (t1 t2)
      (== `(,t1 ,t2) t))))

(define reduceo
  (lambda (t t^)
    (conde
      [(valueo t) (== t t^)]
      [(fresh (t1 t2 t1^)
         (== `(,t1 ,t2) t)
         (not-valueo t1)
         (reduceo t1 t1^)
         (reduceo `(,t1^ ,t2) t^))]
      [(fresh (v1 t2 t2^)
         (== `(,v1 ,t2) t)
         (valueo v1)
         (not-valueo t2)
         (reduceo t2 t2^)
         (reduceo `(,v1 ,t2^) t^))]
      [(fresh (t1 t1^ x t12 v2 x^ t12^)
         (templateo t1 t1^)             ; declarative copyterm
         (== `(,t1 ,v2) t)
         (== `(lambda (,x) ,t12) t1)
         (symbolo x)
         (valueo v2)
         (== `(lambda (,x^) ,t12^) t1^)
         (== x^ v2)                   ; beta reduction via unification
         (reduceo t12^ t^))])))


(module+ test
  (require cKanren/tester)

  (test "templateo-reordering-1"
    (run* (q)
      (fresh (x y a b)
        (== x y)
        (templateo `(,x ,y) `(,a ,b))
        (== q `(,x ,y ,a ,b))))
    '((_.0 _.0 _.1 _.1)))  
  (test "templateo-reordering-2"
;;; Failing test, courtesy of @namin    
    (run* (q)
      (fresh (x y a b)
        (templateo `(,x ,y) `(,a ,b))
        (== x y)
        (== q `(,x ,y ,a ,b))))
    '((_.0 _.0 _.1 _.1)))
  
  (test "templateo-1a" (run* (q) (fresh (x) (templateo `(lambda (,x) ,x) q))) '((lambda (_.0) _.0)))
  (test "templateo-1b"
;;; What should this return? What would it mean to generate the template?
;;; Wouldn't '(_.0 (_.0 _.1 _.2) ... (_.0 (_.1) _.2) (lambda (_.0) _.1) (lambda (_.0) _.0)) be a reasonable answer?
    (run* (q) (fresh (x) (templateo q `(lambda (,x) ,x)))) '(_.0))
  (test "templateo-2" (run* (q) (fresh (x y) (templateo `(lambda (,x) (,y ,x)) q))) '((lambda (_.0) (_.1 _.0))))
  (test "templateo-3"
    (run* (q)
      (fresh (x y z t1 t2 t3)
        (templateo `(lambda (,x) ,x) t1)
        (templateo `(lambda (,x) ,x) t2)
        (templateo `(lambda (,x) ,x) t3)
        (== t1 `(lambda (,y) ,z))
        (== 5 z)
        (== `(,t1 ,t2 ,t3) q)))    
    '(((lambda (5) 5) (lambda (_.0) _.0) (lambda (_.1) _.1))))
  (test "templateo-4"
    (run* (q)
      (fresh (x y z t1 t2 t3)
        (== t1 `(lambda (,y) ,z))
        (== 5 z)
        (== `(,t1 ,t2 ,t3) q)
        (templateo `(lambda (,x) ,x) t2)
        (templateo `(lambda (,x) ,x) t3)
        (templateo `(lambda (,x) ,x) t1)))    
    '(((lambda (5) 5) (lambda (_.0) _.0) (lambda (_.1) _.1))))
  (test "templateo-5"
    (run* (q)
      (fresh (x y z t1 t2 t3)
        (templateo `(lambda (,x) ,x) t2)
        (templateo `(lambda (,x) ,x) t3)
        (== `(,t1 ,t2 ,t3) q)
        (== t1 `(lambda (,y) ,z))
        (== 5 z)
        (templateo `(lambda (,x) ,x) t1)))
    '(((lambda (5) 5) (lambda (_.0) _.0) (lambda (_.1) _.1))))
  
  (test "valueo-1" (run* (q) (fresh (x) (valueo `(lambda (,x) ,x)))) '(_.0))
  (test "valueo-2" (run* (q) (fresh (x y) (valueo `((lambda (,x) ,x) (lambda (,y) ,y))))) '())
  (test "valueo-3" (run* (q) (valueo q)) '(((lambda (_.0) _.1) : (sym _.0))))
  
  (test "not-valueo-1" (run* (q) (fresh (x y) (not-valueo `((lambda (,x) ,x) (lambda (,y) ,y))))) '(_.0))
  (test "not-valueo-2" (run* (q) (fresh (x) (not-valueo `(lambda (,x) ,x)))) '())
  (test "not-valueo-3" (run* (q) (not-valueo q)) '((_.0 _.1)))

  (test "reduceo-1"
    (run 10 (q) (fresh (t t^) (reduceo t t^) (== `(,t ,t^) q)))
    '((((lambda (_.0) _.1) (lambda (_.0) _.1)) : (sym _.0))
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)) : (sym _.0 _.2 _.4))
      (((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)) (lambda (_.6) _.7)) : (sym _.0 _.2 _.4 _.6))
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)) : (sym _.0 _.2 _.4))
      ((((lambda (_.0) _.1) ((lambda (_.2) _.3) (lambda (_.4) _.5))) (lambda (_.6) _.7)) : (sym _.0 _.2 _.4 _.6))
      (((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)) (lambda (_.6) _.7)) : (sym _.0 _.2 _.4 _.6))
      ((((lambda (_.0) _.1) ((lambda (_.2) _.3) (lambda (_.4) _.5))) (lambda (_.6) _.7)) : (sym _.0 _.2 _.4 _.6))
      (((((lambda (_.0) _.1) (lambda (_.2) _.3)) ((lambda (_.4) _.5) (lambda (_.6) _.7))) (lambda (_.8) _.9)) : (sym _.0 _.2 _.4 _.6 _.8))
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)) : (sym _.0 _.2 _.4))
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5)) : (sym _.0 _.2 _.4))))
  (test "reduceo-2"
    (run* (q) (fresh (x y) (reduceo `(lambda (,x) ,x) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-3"
    (run* (q) (fresh (x y t t^) (== `((lambda (,x) ,x) (lambda (,y) ,y)) t) (reduceo t t^) (== `(,t ,t^) q)))
    '(((((lambda (_.0) _.0) (lambda (_.1) _.1)) (lambda (_.1) _.1))
       :
       (sym _.0 _.1))))
  (test "reduceo-4"
    (run* (q) (fresh (x y) (reduceo `((lambda (,x) ,x) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-5"
    (run* (q) (fresh (x y) (reduceo `((lambda (,x) (,x ,x)) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-6"
    (run* (q) (fresh (x y) (reduceo `((lambda (,x) ((,x ,x) (,x ,x))) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-7"
    (run* (q) (fresh (x y) (reduceo `((lambda (,x) ,x) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-8"
    (run* (q) (fresh (x y) (reduceo `((lambda (,x) ((,x ,x) (,x ,x))) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-9"
    (run* (q)
      (fresh (x x^^ z)
        (symbolo x)
        (symbolo x^^)
        (symbolo z)
        (reduceo `((lambda (,z) ((lambda (,x^^) ,x^^) ,z)) (lambda (,x) ,x)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-10"
    (run* (q)
      (fresh (x x^ x^^ y z)
        (symbolo x)
        (symbolo x^)
        (symbolo x^^)
        (symbolo y)
        (symbolo z)
        (reduceo `((lambda (,x^) ,x^) (lambda (,z) ((lambda (,x^^) ,x^^) ,z))) q)))
    '(((lambda (_.0) ((lambda (_.1) _.1) _.0)) : (sym _.0 _.1))))
  (test "reduceo-11a"
    (run* (q)
      (fresh (x x^ x^^ y z)
        (symbolo x)
        (symbolo x^)
        (symbolo x^^)
        (symbolo y)
        (symbolo z)
        (reduceo `((lambda (,x) ,x) ((lambda (,x^) ,x^) (lambda (,z) ((lambda (,x^^) ,x^^) ,z)))) q)))
    '(((lambda (_.0) ((lambda (_.1) _.1) _.0)) : (sym _.0 _.1))))  
  (test "reduceo-11b"
    (run* (q)
      (fresh (x x^ x^^ y z)
        (symbolo x)
        (symbolo x^)
        (symbolo x^^)
        (symbolo y)
        (symbolo z)
        (reduceo `(((lambda (,x^) ,x^) (lambda (,z) ((lambda (,x^^) ,x^^) ,z))) (lambda (,x) ,x)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-12"
    (run* (q)
      (fresh (x x^ x^^ y z)
        (symbolo x)
        (symbolo x^)
        (symbolo x^^)
        (symbolo y)
        (symbolo z)
        (reduceo `((lambda (,x) ,x) ((lambda (,x^) ,x^) (lambda (,z) ((lambda (,x^^) ,x^^) ,z)))) q)))
    '(((lambda (_.0) ((lambda (_.1) _.1) _.0)) : (sym _.0 _.1))))
  (test "reduceo-13"
    (run* (q)
      (fresh (x y z)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (reduceo `(((lambda (,x) ,x) (lambda (,y) ,y)) (lambda (,z) ,z)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-14"
    (run* (q)
      (fresh (x y)
        (symbolo x)
        (symbolo y)
        (reduceo `((lambda (,x) ,x) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-15"
    (run* (q)
      (fresh (x y z w)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (symbolo w)
        (reduceo `(((lambda (,x) ,x) (lambda (,y) ,y)) (lambda (,z) ,w)) q)))
    '(((lambda (_.0) _.1) : (sym _.0 _.1))))

  ;; (test "reduceo-omega"
  ;;   ; diverges, as it should!!    
  ;;   (run 1 (q) (fresh (x y) (reduceo `((lambda (,x) ((,x ,x) (,x ,x))) (lambda (,y) ((,y ,y) (,y ,y)))) q)))
  ;;   'bottom)
)
