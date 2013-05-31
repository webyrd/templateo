#lang cKanren

(require cKanren/miniKanren)
(require cKanren/neq)
(require cKanren/absento)
(require cKanren/template)

(provide (all-defined-out))

;;; Untyped lambda-calculus rules from p.72 of Pierce's 'Types and Programming Languages'.
;;;
;;; This approach doesn't to work with open terms, due to the templateo:
;;; reducing ((lambda (_.0) _.1) (lambda (_.2) _.3)) yields (lambda (_.4) _.5)

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
         (not-valueo t2)
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

;; (define reduceo
;;   (lambda (t t^)
;;     (conde
;;       [(valueo t) (== t t^)]
;;       [(fresh (t1 t2 t1^)
;;          (== `(,t1 ,t2) t)
;;          (not-valueo t1)
;;          (not-valueo t2)
;;          (reduceo t1 t1^)
;;          (reduceo `(,t1^ ,t2) t^))]
;;       [(fresh (v1 t2 t2^)
;;          (== `(,v1 ,t2) t)
;;          (valueo v1)
;;          (not-valueo t2)
;;          (reduceo t2 t2^)
;;          (reduceo `(,v1 ,t2^) t^))]
;;       [(fresh (t1 t1^ x t12 v2 x^ t12^)
;;          (templateo t1 t1^)             ; declarative copyterm
;;          (== `(,t1 ,v2) t)
;;          (== `(lambda (,x) ,t12) t1)
;;          (valueo v2)
;;          (== `(lambda (,x^) ,t12^) t1^)
;;          (== x^ v2)                   ; beta reduction via unification
;;          (reduceo t12^ t^))])))



(module+ test
  (require cKanren/tester)

  (test "templateo-1" (run* (q) (fresh (x) (templateo `(lambda (,x) ,x) q))) '((lambda (_.0) _.0)))
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
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5))
       :
       (sym _.0 _.2 _.4))
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5))
       :
       (sym _.0 _.2 _.4))
      ((((lambda (_.0) _.1) ((lambda (_.2) _.3) (lambda (_.4) _.5)))
        (lambda (_.6) _.7))
       :
       (sym _.0 _.2 _.4 _.6))
      (((((lambda (_.0) _.1) (lambda (_.2) _.3))
         ((lambda (_.4) _.5) (lambda (_.6) _.7)))
        (lambda (_.8) _.9))
       :
       (sym _.0 _.2 _.4 _.6 _.8))
      ((((lambda (_.0) _.1) ((lambda (_.2) _.3) (lambda (_.4) _.5)))
        (lambda (_.6) _.7))
       :
       (sym _.0 _.2 _.4 _.6))
      (((((lambda (_.0) _.1) (lambda (_.2) _.3))
         ((lambda (_.4) _.5) (lambda (_.6) _.7)))
        (lambda (_.8) _.9))
       :
       (sym _.0 _.2 _.4 _.6 _.8))
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5))
       :
       (sym _.0 _.2 _.4))
      ((((lambda (_.0) _.1) (lambda (_.2) _.3)) (lambda (_.4) _.5))
       :
       (sym _.0 _.2 _.4))
      (((((lambda (_.0) _.1) (lambda (_.2) _.3))
         ((lambda (_.4) _.5) (lambda (_.6) _.7)))
        (lambda (_.8) _.9))
       :
       (sym _.0 _.2 _.4 _.6 _.8))))
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

  ;; (test "reduceo-omega"
  ;;   ; diverges, as it should!!    
  ;;   (run 1 (q) (fresh (x y) (reduceo `((lambda (,x) ((,x ,x) (,x ,x))) (lambda (,y) ((,y ,y) (,y ,y)))) q)))
  ;;   'bottom)
)
