#lang cKanren

(require cKanren/miniKanren)
(require cKanren/neq)
(require cKanren/absento)
(require cKanren/template)

(provide (all-defined-out))

;;; Untyped lambda-calculus rules from p.72 of Pierce's 'Types and Programming Languages'.
;;;
;;; This reducer doesn't handle shadowing properly.  Rather, it assumes Barendregt convention.
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



;;; type inferencer for Hindley-Milner, with polymorphic 'let' using templateo.
;;;
;;; Rules from pages 103 and 333 of Pierce.  Also, http://okmij.org/ftp/ML/generalization.html

(define lookupo
  (lambda (gamma x t tag old-gamma)    
    (fresh (x^ t^ tag^ gamma^ old-gamma^)      
      (== `((,tag^ ,x^ ,t^ . ,old-gamma^) . ,gamma^) gamma)      
      (conde
        [(== x x^)
         (== t t^)
         (== tag tag^)
         (== old-gamma^ old-gamma)]
        [(=/= x x^)
         (lookupo gamma^ x t tag old-gamma)]))))

(define !-
  (lambda (gamma e t)
    (conde
      [(numbero e) (== 'int t)]
      [(symbolo e)
       (fresh (tag t^ old-gamma old-gamma^)         
         (lookupo gamma e t^ tag old-gamma)
         (conde
           [(== 'non-generic tag)
            (== t^ t)]
           [(== 'generic tag)
            (templateo `(,old-gamma ,t^) `(,old-gamma^ ,t)) ;; copy the generic template
            (== old-gamma old-gamma^)]))]
      [(conde
         [(== #t e)]
         [(== #f e)])
       (== 'bool t)]
      [(fresh (e1)
         (== `(zero? ,e1) e)
         (absento 'zero? gamma)
         (== 'bool t)
         (!- gamma e1 'int))]
      [(fresh (e1)
         (== `(sub1 ,e1) e)
         (absento 'sub1 gamma)
         (== 'int t)
         (!- gamma e1 'int))]
      [(fresh (e1 t2)
         (== `(car ,e1) e)
         (absento 'car gamma)
         (!- gamma e1 `(pair ,t ,t2)))]
      [(fresh (e1 t2)
         (== `(cdr ,e1) e)
         (absento 'cdr gamma)
         (!- gamma e1 `(pair ,t2 ,t)))]      
      [(fresh (x body t1 t2)
         (== `(lambda (,x) ,body) e)
         (symbolo x)
         (absento 'lambda gamma)
         (== `(-> ,t1 ,t2) t)
         (!- `((non-generic ,x ,t1) . ,gamma) body t2))]
;;;
      [(fresh (x e1 body t1 gamma^) ; polymorphic let
         (== `(let ((,x ,e1)) ,body) e)
         (symbolo x)
         (absento 'let gamma)
         (!- gamma e1 t1) ; make sure 'e1' has a valid type, regardless of whether 'x' appears in 'body'
         (== `((generic ,x ,t1 . ,gamma) . ,gamma) gamma^)         
         (!- gamma^ body t))]
;;;
      [(fresh (e1 e2)
         (== `(* ,e1 ,e2) e)
         (absento '* gamma)
         (== 'int t)
         (!- gamma e1 'int)
         (!- gamma e2 'int))]
      [(fresh (e1 e2 t1 t2)
         (== `(cons ,e1 ,e2) e)
         (absento 'cons gamma)
         (== `(pair ,t1 ,t2) t)
         (!- gamma e1 t1)
         (!- gamma e2 t2))]      
      [(fresh (e1 e2 t1)
         (== `(,e1 ,e2) e)
         (!- gamma e1 `(-> ,t1 ,t))
         (!- gamma e2 t1))]
      [(fresh (e1 e2 e3)
         (== `(if ,e1 ,e2 ,e3) e)
         (absento 'if gamma)
         (!- gamma e1 'bool)
         (!- gamma e2 t)
         (!- gamma e3 t))])))


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
;;; Previously failing test, courtesy of @namin
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
  (test "reduceo-16-a"
;;; show that shadowing isn't handled properly
;;; since the resulting term after the beta step isn't legal:
;;; (lambda ((lambda (,y) ,y)) (lambda (,y) ,y))
    (run* (q)
      (fresh (x y)
        (symbolo x)
        (symbolo y)
        (reduceo `((lambda (,x) (lambda (,x) ,x)) (lambda (,y) ,y)) q)))
    '())
  (test "reduceo-16-b"
    (run* (q)
      (fresh (x y z)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (reduceo `((lambda (,x) (lambda (,z) ,x)) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) (lambda (_.1) _.1)) : (sym _.0 _.1))))
  (test "reduceo-16-c"
    (run* (q)
      (fresh (x y z)
        (symbolo x)
        (symbolo y)
        (symbolo z)        
        (reduceo `((lambda (,x) (lambda (,z) ,z)) (lambda (,y) ,y)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))
  (test "reduceo-17"
;;; show that shadowing isn't handled properly
    (run* (q)
      (fresh (x y z w)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (symbolo w)
        (reduceo `(((lambda (,x) (lambda (,x) ,x)) (lambda (,y) ,y)) (lambda (,z) ,w)) q)))
    '())
  (test "reduceo-18"
;;; show that shadowing isn't handled properly    
    (run* (q)
      (fresh (x y z)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (reduceo `(((lambda (,x) (lambda (,x) ,x)) (lambda (,y) ,y)) (lambda (,y) ,y)) q)))
    '())
  (test "reduceo-19"
    (run* (q)
      (fresh (x)
        (symbolo x)
        (reduceo `(lambda (,x) (lambda (,x) ,x)) q)))
    '(((lambda (_.0) (lambda (_.0) _.0)) : (sym _.0))))
  (test "reduceo-20"
    (run* (q)
      (fresh (x y z w)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (symbolo w)
        (reduceo `((lambda (,y) (lambda (,x) (lambda (,x) ,x))) (lambda (,z) ,z)) q)))
    '(((lambda (_.0) (lambda (_.0) _.0)) : (sym _.0))))
  (test "reduceo-21"
;;; show that shadowing isn't handled properly    
    (run* (q)
      (fresh (x y z w)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (symbolo w)
        (reduceo `((lambda (,y) ((lambda (,x) (lambda (,x) ,x)) ,y)) (lambda (,z) ,z)) q)))
    '())
  (test "reduceo-22"
    (run* (q)
      (fresh (x y z w)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (symbolo w)
        (reduceo `((lambda (,y) ((lambda (,x) (lambda (,w) ,x)) ,y)) (lambda (,z) ,z)) q)))
    '(((lambda (_.0) (lambda (_.1) _.1)) : (sym _.0 _.1))))
  (test "reduceo-23"
    (run* (q)
      (fresh (x y z w)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (symbolo w)
        (reduceo `((lambda (,y) ((lambda (,x) (lambda (,w) ,w)) ,y)) (lambda (,z) ,z)) q)))
    '(((lambda (_.0) _.0) : (sym _.0))))

  (test "reduceo-Accattoli"
;;; counter example to naive "freshness" by Beniamino Accattoli ([TYPES] mailing list, Fri, Apr 27, 2012 at 4:19 PM)
;;
;;  > Dear Philip,
;; > My first observation has been that it is easy to break "freshness",
;; > just consider the reduction of \delta \delta. But in this case is
;; > however possible to reduce without ever using alpha.
;; >
;; > If I understand the problem correctly, this is a counter-example for
;; > both freshness and alpha:
;; >
;; > (\l z.zz) (\ly.\lx.yx)
;; > ->
;; > (\ly.\lx.yx) (\ly.\lx.yx)
;; > ->
;; > \lx.((\ly.\lx.yx)x)
;; > -/->
;; >
;; > Best,
;; > Beniamino Accattoli
    (run* (q)
      (fresh (x y z)
        (symbolo x)
        (symbolo y)
        (symbolo z)
        (reduceo `((lambda (,z) (,z ,z)) (lambda (,y) (lambda (,x) (,y ,x)))) q)))
    '(((lambda (_.0) ((lambda (_.1) (lambda (_.2) (_.1 _.2))) _.0)) : (sym _.0 _.1 _.2))))
  
  ;; (test "reduceo-omega"
  ;;   ; diverges, as it should!!    
  ;;   (run 1 (q) (fresh (x y) (reduceo `((lambda (,x) ((,x ,x) (,x ,x))) (lambda (,y) ((,y ,y) (,y ,y)))) q)))
  ;;   'bottom)

  (test "lookupo-1"
    (run* (q) (lookupo `((non-generic x int) (non-generic y bool) (non-generic x bool)) 'x q 'non-generic '()))
    '(int))

  (test "lookupo-2"
    (run* (q) (fresh (x) (lookupo `((non-generic x int) (non-generic y bool) (non-generic x bool)) x q 'non-generic '())))
    '(int bool))

  (test "lookupo-3"
    (run* (q) (lookupo `((non-generic x int) (non-generic y bool) (non-generic x bool)) 'z q 'non-generic '()))
    '())

  (test "lookupo-4"
    (run 5 (q) (fresh (gamma x t tag old-gamma) (lookupo gamma x t tag old-gamma) (== `(,gamma ,x ,t ,tag ,old-gamma) q)))
    '((((_.0 _.1 _.2 . _.3) . _.4) _.1 _.2 _.0 _.3)
      ((((_.0 _.1 _.2 . _.3) (_.4 _.5 _.6 . _.7) . _.8) _.5 _.6 _.4 _.7) : (=/= ((_.1 . _.5))))
      ((((_.0 _.1 _.2 . _.3) (_.4 _.5 _.6 . _.7) (_.8 _.9 _.10 . _.11) . _.12) _.9 _.10 _.8 _.11) : (=/= ((_.1 . _.9)) ((_.5 . _.9))))
      ((((_.0 _.1 _.2 . _.3) (_.4 _.5 _.6 . _.7) (_.8 _.9 _.10 . _.11) (_.12 _.13 _.14 . _.15) . _.16) _.13 _.14 _.12 _.15) : (=/= ((_.1 . _.13)) ((_.13 . _.5)) ((_.13 . _.9))))
      ((((_.0 _.1 _.2 . _.3) (_.4 _.5 _.6 . _.7) (_.8 _.9 _.10 . _.11) (_.12 _.13 _.14 . _.15) (_.16 _.17 _.18 . _.19) . _.20) _.17 _.18 _.16 _.19) : (=/= ((_.1 . _.17)) ((_.13 . _.17)) ((_.17 . _.5)) ((_.17 . _.9))))))

  
  (test "!-1"
    (run* (q) (!- '() '(lambda (y) y) q))
    '((-> _.0 _.0)))

  (test "!-2"
    (run* (q) (!- '() '((lambda (y) y) (lambda (z) z)) q))
    '((-> _.0 _.0)))

  (test "!-3"
    (run* (q) (!- '() '((lambda (y) y) (lambda (z) (lambda (w) (w z)))) q))
    '(((-> _.0 (-> (-> _.0 _.1) _.1)) : (absento (lambda _.0)))))

  (test "!-4"
    (run* (q) (!- '() '(lambda (y) (y y)) q))
    '())

  (test "!-5"
    (run* (q) (!- '() '5 q))
    '(int))

  (test "!-6"
    (run* (q) (!- '() '#t q))
    '(bool))

  (test "!-7"
    (run* (q) (!- '() '(zero? 5) q))
    '(bool))

  (test "!-8"
    (run* (q) (!- '() '(zero? (sub1 5)) q))
    '(bool))
  
  (test "!-9"
    (run* (q) (!- '() '(* 3 (sub1 5)) q))
    '(int))

  (test "!-10"
    (run* (q) (!- '() '(if #t 3 4) q))
    '(int))
  
  (test "!-11"
    (run* (q) (!- '() '(if (zero? (sub1 5)) (* 3 4) (sub1 6)) q))
    '(int))

  (test "!-12"
    (run* (q) (!- '() '(let ((x 3)) #t) q))
    '(bool))
  
  (test "!-13"
    (run* (q) (!- '() '(let ((x 3)) x) q))
    '(int))
  
  (test "!-14"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f 5)) q))
    '(int))

  (test "!-16"
    (run* (q) (!- '() '(let ((f (lambda (x) (x x)))) 3) q))
    '())
  

  (test "!-18"
;;; test from http://okmij.org/ftp/ML/generalization.html
    (run* (q) (!- '() '(lambda (x) (let ((y (lambda (z) z))) y)) q))
    '(((-> _.0 (-> _.1 _.1)) : (absento (lambda _.0) (let _.0)))))

  (test "16.1"
    (run* (q)
      (fresh (x g g^ t t^)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== `(,t) g)
        (== g g^)
        (== `(,t ,t^) q)))
    '((_.0 _.0)))
 
  (test "16.3"
    (run* (q)
      (fresh (x g g^ t t^)
        (== g g^)
        (== `(,t) g)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== `(,t ,t^) q)))
    '((_.0 _.0)))
  
  (test "templateo-96a"
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== `(-> ,t1 ,t2) t)
        (== `((x ,t1)) g)
        (== `(,t ,t^) q)
        (== g g^)))
    '(((-> _.0 _.1) (-> _.0 _.2))))

  (test "templateo-96b"
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (== g g^)
        (== `(-> ,t1 ,t2) t)
        (== `((x ,t1)) g)
        (== `(,t ,t^) q)
        (templateo `(,g ,t) `(,g^ ,t^))))
    '(((-> _.0 _.1) (-> _.0 _.2))))



  
  (test "templateo-99a"
    (run* (q)
      (fresh (x xt y g g^)
        (== `((,x ,xt) (,y ,xt)) g)
        (== g g^)
        (templateo `(,g ,xt) `(,g^ ,xt))
        (== `(,x ,xt ,y ,g ,g^) q)))
    '((_.0 _.1 _.2 ((_.0 _.1) (_.2 _.1)) ((_.0 _.1) (_.2 _.1)))))

  (test "templateo-99b"
    (run* (q)
      (fresh (x xt y g g^)
        (== `((,x ,xt) (,y ,xt)) g)
        (templateo `(,g ,xt) `(,g^ ,xt))
        (== g g^)
        (== `(,x ,xt ,y ,g ,g^) q)))
    '((_.0 _.1 _.2 ((_.0 _.1) (_.2 _.1)) ((_.0 _.1) (_.2 _.1)))))  

  (test "templateo-99c"
    (run* (q)
      (fresh (x xt y g g^)
        (templateo `(,g ,xt) `(,g^ ,xt))
        (== `((,x ,xt) (,y ,xt)) g)
        (== g g^)
        (== `(,x ,xt ,y ,g ,g^) q)))
    '((_.0 _.1 _.2 ((_.0 _.1) (_.2 _.1)) ((_.0 _.1) (_.2 _.1)))))
   
  (test "templateo-99d"
    (run* (q)
      (fresh (x xt y g g^)
        (templateo `(,g ,xt) `(,g^ ,xt))
        (== `((,x ,xt) (,y ,xt)) g)
        (== `(,x ,xt ,y ,g ,g^) q)
        (== g g^)))
    '((_.0 _.1 _.2 ((_.0 _.1) (_.2 _.1)) ((_.0 _.1) (_.2 _.1)))))

  (test "templateo-99e"
    (run* (q)
      (fresh (x xt y g g^)
        (== `((,x ,xt) (,y ,xt)) g)
        (== `(,x ,xt ,y ,g ,g^) q)
        (== g g^)
        (templateo `(,g ,xt) `(,g^ ,xt))))
    '((_.0 _.1 _.2 ((_.0 _.1) (_.2 _.1)) ((_.0 _.1) (_.2 _.1)))))

  (test "templateo-99f"
    (run* (q)
      (fresh (x xt y g g^)
        (== g g^)
        (== `((,x ,xt) (,y ,xt)) g)
        (== `(,x ,xt ,y ,g ,g^) q)
        (templateo `(,g ,xt) `(,g^ ,xt))))
    '((_.0 _.1 _.2 ((_.0 _.1) (_.2 _.1)) ((_.0 _.1) (_.2 _.1)))))  

  (test "templateo-98a"
    (run* (q)
      (fresh (x xt y yt g g^ t t^)
        (== g g^)
        (== `((,x ,xt) (,y ,yt)) g)
        (== `(,x ,xt ,y ,yt ,g ,g^ ,t ,t^) q)
        (templateo `(,g ,t) `(,g^ ,t^))))
    '((_.0 _.1 _.2 _.3 ((_.0 _.1) (_.2 _.3)) ((_.0 _.1) (_.2 _.3)) _.4 _.5)))

  (test "templateo-98b"
    (run* (q)
      (fresh (x xt y yt g g^ t t^)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== g g^)
        (== `((,x ,xt) (,y ,yt)) g)
        (== `(,x ,xt ,y ,yt ,g ,g^ ,t ,t^) q)))
    '((_.0 _.1 _.2 _.3 ((_.0 _.1) (_.2 _.3)) ((_.0 _.1) (_.2 _.3)) _.4 _.5)))

  (test "!-17"
;;; test from http://okmij.org/ftp/ML/generalization.html
    (run* (q) (!- '() '(lambda (x) (let ((y x)) y)) q))
    '(((-> _.0 _.0) : (absento (let _.0)))))

  (test "templateo-97a"
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (== g g^)
        (== `(-> ,t1 ,t2) t)
        (== `((x ,t1)) g)
        (== `(,x ,t ,t1 ,t2 ,t^ ,g ,g^) q)
        (templateo `(,g ,t) `(,g^ ,t^))))
    '((_.0 (-> _.1 _.2) _.1 _.2 (-> _.1 _.3) ((x _.1)) ((x _.1)))))

  (test "templateo-97b"
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== `(-> ,t1 ,t2) t)
        (== `((x ,t1)) g)
        (== `(,x ,t ,t1 ,t2 ,t^ ,g ,g^) q)
        (== g g^)))
    '((_.0 (-> _.1 _.2) _.1 _.2 (-> _.1 _.3) ((x _.1)) ((x _.1)))))
  
  (test "templateo-97c"
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (== g g^)
        (== `(-> ,t1 ,t2) t)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== `((x ,t1)) g)
        (== `(,x ,t ,t1 ,t2 ,t^ ,g ,g^) q)))
    '((_.0 (-> _.1 _.2) _.1 _.2 (-> _.1 _.3) ((x _.1)) ((x _.1)))))

  (test "templateo-97d"
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== g g^)
        (== `(-> ,t1 ,t2) t)
        (== `((x ,t1)) g)
        (== `(,x ,t ,t1 ,t2 ,t^ ,g ,g^) q)))
    '((_.0 (-> _.1 _.2) _.1 _.2 (-> _.1 _.3) ((x _.1)) ((x _.1)))))  

  (test "!-pair-1"
    (run* (q) (!- '() '(cons 3 #t) q))
    '((pair int bool)))

  (test "!-pair-2"
    (run* (q) (!- '() '(car (cons 3 #t)) q))
    '(int))

  (test "!-pair-3"
    (run* (q) (!- '() '(cdr (cons 3 #t)) q))
    '(bool))

  (test "!-pair-4"
    (run* (q) (!- '() '(cons (cons #f 6) (cons 3 #t)) q))
    '((pair (pair bool int) (pair int bool))))
  
  (test "!-pair-5"
    (run* (q) (!- '() '(cdr (cons (cons #f 6) (cons 3 #t))) q))
    '((pair int bool)))
  
  (test "!-15a"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f 5)) q))
    '(int))

  (test "!-15b"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f #t)) q))
    '(bool))

  (test "!-15c"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f (zero? 5))) q))
    '(bool))

  (test "!-15d"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f (f (zero? 5)))) q))
    '(bool))

  (test "!-15e"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f (f (sub1 5)))) q))
    '(int))

  (test "!-15h"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f (f 5))) q))
    '(int))
  
  (test "!-15f"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (if (f 5) (f 6) (f 7))) q))
    '())
  
  (test "!-15g"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (if (f #t) (f 6) (f 7))) q))
    '(int))
  
  (test "!-15"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f (zero? (f 5)))) q))
    '(bool))

;;; Tests from https://github.com/namin/TAPL-in-miniKanren-cKanren-core.logic/blob/master/clojure-tapl/tapl/test/tapl/test/letpoly.clj  
  (test "!-40"
    (run* (q) (!- '() '(lambda (x) (lambda (y) (x y))) q))
    '(((-> (-> _.0 _.1) (-> _.0 _.1)) : (absento (lambda _.0) (lambda _.1)))))

  (test "!-41"
    (run* (q) (!- '() '(lambda (f) (lambda (a) ((lambda (d) f) (f a)))) q))
    '(((-> (-> _.0 _.1) (-> _.0 (-> _.0 _.1))) : (absento (lambda _.0) (lambda _.1)))))

  (test "!-42"
    (run* (q) (!- '() '(let ((a (lambda (a) a))) a) q))
    '((-> _.0 _.0)))  

  (test "!-43"
    (run* (q) (!- '() '(let ((a (lambda (a) a))) (a a)) q))
    '((-> _.0 _.0)))  

  (test "!-44"
    (run* (q) (!- '() '(lambda (a) (let ((b a)) b)) q))
    '(((-> _.0 _.0) : (absento (let _.0)))))

  (test "!-45"
    (run* (q) (!- '() '(lambda (f) (lambda (a) (let ((id (lambda (x) x))) ((lambda (d) (id f)) ((id f) (id a)))))) q))
    '(((-> (-> _.0 _.1) (-> _.0 (-> _.0 _.1))) : (absento (lambda _.0) (lambda _.1) (let _.0) (let _.1)))))

  (test "!-46"
    (run* (q) (!- '() '(lambda (f) (lambda (a) (let ((id (lambda (a) a))) ((lambda (d) (id f)) ((id f) (id a)))))) q))
    '(((-> (-> _.0 _.1) (-> _.0 (-> _.0 _.1))) : (absento (lambda _.0) (lambda _.1) (let _.0) (let _.1)))))
  
  (test "!-21"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) f) q))
    '((-> _.0 _.0)))
  
  (test "!-19"
    (run 1 (q) (fresh (lam) (== `(let ((f ,lam)) (f (f 5))) q)) (!- '() q 'int))
    '(((let ((f (lambda (_.0) _.1))) (f (f 5))) : (num _.1) (sym _.0))))

  (test "!-20"
    (run 1 (q) (fresh (lam) (== `(let ((f ,lam)) (if (f #t) (f 6) (f 7))) q)) (!- '() q 'int))
    '(((let ((f (lambda (_.0) _.0))) (if (f #t) (f 6) (f 7))) : (sym _.0))))
  
  (test "!-23"
;;; self-application via let polymorphism.  I guess that's a thing???
    (run* (q)
      (!- '() '(let ((f (lambda (x) 5))) (f f)) q))
    '(int))

  (test "!-23b"
;;; self-application without let poly doesn't type check!
    (run* (q)
      (!- '() '((lambda (f) (f f)) (lambda (x) 5)) q))
    '())

  (test "!-23c"
    (run* (q)
      (!- '() '((lambda (x) (x x)) (lambda (x) (x x))) q))
    '())

  (test "!-23d"
;;; self-application via let polymorphism.  I guess that's a thing???    
    (run* (q)
      (!- '() '(let ((f (lambda (x) x))) (f f)) q))
    '((-> _.0 _.0)))

  (test "!-23e"
;;; self-application without let poly doesn't type check!    
    (run* (q)
      (!- '() '((lambda (f) (f f)) (lambda (x) x)) q))
    '())

  (test "!-23f"
;;; omega still doesn't typecheck    
    (run* (q)
      (!- '() '(let ((f (lambda (x) (x x)))) (f f)) q))
    '())
  
  (test "!-23g"
    (run* (q)
      (!- '() '((lambda (x) (x x)) (lambda (x) (x x))) q))
    '())

  (test "!-23h"
    (run* (q)
      (!- '() '(let ((f (lambda (x) (x 5)))) (f f)) q))
    '())
  
  
  (test "!-29"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             5)
          q))
    '(int))

  (test "!-30"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               5))
          q))
    '(int))

  (test "!-31"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f1 5)))
          q))
    '(int))

  (test "!-37"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               f1))
          q))
    '((-> _.0 _.0)))
  
  (test "!-36"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               f0))
          q))
    '((-> _.0 _.0)))
  
  (test "!-32"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f0 5)))
          q))
    '(int))

  (test "!-33"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f0 (f1 5))))
          q))
    '(int))

  (test "!-34"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) y)))
               (f0 (f0 (f1 (f1 (f0 (f1 (f0 5)))))))))
          q))
    '(int))
  
  (test "!-28"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) f0)))
               5))
          q))
    '(int))
  
  (test "!-27"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 y))))
               5))
          q))
    '(int))
  
  (test "!-26"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               5))
          q))
    '(int))
  
  (test "!-25"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               f1))
          q))
    '((-> _.0 _.0)))
  
  (test "!-24a"
    (run* (q)
      (!- '() '(let ((f0 (lambda (x) x)))
                 (f0 (lambda (z) z))) q))
    '((-> _.0 _.0)))

  (test "!-24b"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (f1 (lambda (z) z))))
          q))
    '((-> _.0 _.0)))

  (test "!-24c"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (f2 (lambda (z) z)))))
          q))
    '((-> _.0 _.0)))

  (test "!-24d"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (f3 (lambda (z) z))))))
          q))
    '((-> _.0 _.0)))

  (test "!-24e"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (let ((f4 (lambda (y) (f3 (f3 y)))))
                     (f4 (lambda (z) z)))))))
          q))
    '((-> _.0 _.0)))  

  (test "!-24f"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) x)))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (let ((f4 (lambda (y) (f3 (f3 y)))))
                     (let ((f5 (lambda (y) (f4 (f4 y)))))
                       (f5 (lambda (z) z))))))))
          q))
    '((-> _.0 _.0)))

  (test "!-30a"
    (run* (q)
      (!- '() '(let ((f0 (lambda (x) (cons x x))))
                 (f0 (lambda (z) z))) q))
    '((pair (-> _.0 _.0) (-> _.0 _.0))))

  (test "!-30b"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) (cons x x))))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (f1 (lambda (z) z))))
          q))
    '((pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))

  (test "!-30c"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) (cons x x))))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (f2 (lambda (z) z)))))
          q))
    '((pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))))

  (test "!-30d"
    (run* (q)
      (!- '()
          '(let ((f0 (lambda (x) (cons x x))))
             (let ((f1 (lambda (y) (f0 (f0 y)))))
               (let ((f2 (lambda (y) (f1 (f1 y)))))
                 (let ((f3 (lambda (y) (f2 (f2 y)))))
                   (f3 (lambda (z) z))))))
          q))
    '((pair (pair (pair (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))) (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))))) (pair (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))) (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))))) (pair (pair (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))) (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))))) (pair (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))) (pair (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))))) (pair (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))) (pair (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0))) (pair (pair (-> _.0 _.0) (-> _.0 _.0)) (pair (-> _.0 _.0) (-> _.0 _.0)))))))))))

; Seems like these two are too expensive to run!
  ;; (test "!-30e"
  ;;   (run* (q)
  ;;     (!- '()
  ;;         '(let ((f0 (lambda (x) (cons x x))))
  ;;            (let ((f1 (lambda (y) (f0 (f0 y)))))
  ;;              (let ((f2 (lambda (y) (f1 (f1 y)))))
  ;;                (let ((f3 (lambda (y) (f2 (f2 y)))))
  ;;                  (let ((f4 (lambda (y) (f3 (f3 y)))))
  ;;                    (f4 (lambda (z) z)))))))
  ;;         q))
  ;;   '???)

  ;; (test "!-30f"
  ;;   (run* (q)
  ;;     (!- '()
  ;;         '(let ((f0 (lambda (x) (cons x x))))
  ;;            (let ((f1 (lambda (y) (f0 (f0 y)))))
  ;;              (let ((f2 (lambda (y) (f1 (f1 y)))))
  ;;                (let ((f3 (lambda (y) (f2 (f2 y)))))
  ;;                  (let ((f4 (lambda (y) (f3 (f3 y)))))
  ;;                    (let ((f5 (lambda (y) (f4 (f4 y)))))
  ;;                      (f5 (lambda (z) z))))))))
  ;;         q))
  ;;   '???)

  
  (test "!-18"
    (run 50 (q) (!- '() q 'int))
    '((_.0 : (num _.0)) ((sub1 _.0) : (num _.0)) ((sub1 (sub1 _.0)) : (num _.0)) ((sub1 (sub1 (sub1 _.0))) : (num _.0)) ((let ((_.0 _.1)) _.2) : (num _.1 _.2) (sym _.0)) ((sub1 (sub1 (sub1 (sub1 _.0)))) : (num _.0)) ((* _.0 _.1) : (num _.0 _.1)) ((sub1 (let ((_.0 _.1)) _.2)) : (num _.1 _.2) (sym _.0)) ((let ((_.0 #t)) _.1) : (num _.1) (sym _.0)) ((sub1 (sub1 (sub1 (sub1 (sub1 _.0))))) : (num _.0)) ((sub1 (* _.0 _.1)) : (num _.0 _.1)) ((sub1 (sub1 (let ((_.0 _.1)) _.2))) : (num _.1 _.2) (sym _.0)) ((car (cons _.0 _.1)) : (num _.0 _.1)) ((let ((_.0 #f)) _.1) : (num _.1) (sym _.0)) ((let ((_.0 _.1)) _.0) : (num _.1) (sym _.0)) ((let ((_.0 _.1)) (sub1 _.2)) : (=/= ((_.0 . sub1))) (num _.1 _.2) (sym _.0)) ((sub1 (let ((_.0 #t)) _.1)) : (num _.1) (sym _.0)) ((sub1 (sub1 (sub1 (sub1 (sub1 (sub1 _.0)))))) : (num _.0)) ((sub1 (sub1 (* _.0 _.1))) : (num _.0 _.1)) ((cdr (cons _.0 _.1)) : (num _.0 _.1)) ((* _.0 (sub1 _.1)) : (num _.0 _.1)) ((sub1 (sub1 (sub1 (let ((_.0 _.1)) _.2)))) : (num _.1 _.2) (sym _.0)) ((sub1 (car (cons _.0 _.1))) : (num _.0 _.1)) ((if #t _.0 _.1) : (num _.0 _.1)) ((* (sub1 _.0) _.1) : (num _.0 _.1)) ((sub1 (let ((_.0 #f)) _.1)) : (num _.1) (sym _.0)) ((let ((_.0 (zero? _.1))) _.2) : (num _.1 _.2) (sym _.0)) ((sub1 (let ((_.0 _.1)) _.0)) : (num _.1) (sym _.0)) ((car (cons _.0 #t)) : (num _.0)) ((sub1 (let ((_.0 _.1)) (sub1 _.2))) : (=/= ((_.0 . sub1))) (num _.1 _.2) (sym _.0)) ((let ((_.0 #t)) (sub1 _.1)) : (=/= ((_.0 . sub1))) (num _.1) (sym _.0)) ((sub1 (sub1 (let ((_.0 #t)) _.1))) : (num _.1) (sym _.0)) ((sub1 (sub1 (sub1 (sub1 (sub1 (sub1 (sub1 _.0))))))) : (num _.0)) ((let ((_.0 _.1)) (sub1 _.0)) : (=/= ((_.0 . sub1))) (num _.1) (sym _.0)) ((car (cons _.0 #f)) : (num _.0)) ((sub1 (sub1 (sub1 (* _.0 _.1)))) : (num _.0 _.1)) ((let ((_.0 _.1)) (sub1 (sub1 _.2))) : (=/= ((_.0 . sub1))) (num _.1 _.2) (sym _.0)) ((if #f _.0 _.1) : (num _.0 _.1)) ((sub1 (cdr (cons _.0 _.1))) : (num _.0 _.1)) ((sub1 (* _.0 (sub1 _.1))) : (num _.0 _.1)) ((sub1 (sub1 (sub1 (sub1 (let ((_.0 _.1)) _.2))))) : (num _.1 _.2) (sym _.0)) ((sub1 (sub1 (car (cons _.0 _.1)))) : (num _.0 _.1)) ((sub1 (if #t _.0 _.1)) : (num _.0 _.1)) ((sub1 (* (sub1 _.0) _.1)) : (num _.0 _.1)) ((car (cons (sub1 _.0) _.1)) : (num _.0 _.1)) ((car (cons _.0 (zero? _.1))) : (num _.0 _.1)) ((sub1 (sub1 (let ((_.0 #f)) _.1))) : (num _.1) (sym _.0)) ((sub1 (let ((_.0 (zero? _.1))) _.2)) : (num _.1 _.2) (sym _.0)) ((sub1 (sub1 (let ((_.0 _.1)) _.0))) : (num _.1) (sym _.0)) (((lambda (_.0) _.1) _.2) : (num _.1 _.2) (sym _.0))))


;;; This test is *slow*, due to the number of forms handled by the inferencer.  At least comment out pairs if you want to do a run 10!
;;   (test "!-22"
;; ;;; generate expressions with polymorphic let
;; ;;; this test takes a few seconds to run    
;;     (run 1 (q)
;;       (!- '() q 'int)
;;       (fresh (x rest body)
;;         (== `(let ((,x (lambda . ,rest))) ,body) q)
;;         (membero x body)))
;;     '(((let ((_.0 (lambda (_.1) _.2))) (let ((_.0 _.3)) _.0)) : (=/= ((_.0 . let))) (num _.2 _.3) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 _.3)) : (num _.2 _.3) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 #t)) : (num _.2) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 #f)) : (num _.2) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 _.0)) : (num _.2) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 _.0)) : (num _.2) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 (zero? _.3))) : (=/= ((_.0 . zero?))) (num _.2 _.3) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 (sub1 _.3))) : (=/= ((_.0 . sub1))) (num _.2 _.3) (sym _.0 _.1))
;;       ((let ((_.0 (lambda (_.1) _.2))) ((lambda (_.3) _.4) _.0)) : (=/= ((_.0 . lambda))) (num _.2 _.4) (sym _.0 _.1 _.3))
;;       ((let ((_.0 (lambda (_.1) _.2))) (_.0 (lambda (_.3) _.4))) : (=/= ((_.0 . lambda))) (num _.2 _.4) (sym _.0 _.1 _.3))))
  
)
