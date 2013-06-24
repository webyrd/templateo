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
;;; Rules from pages 103 and 333 of Pierce.

(define lookupo
  (lambda (gamma x t tag)
    (fresh (x^ t^ gamma^)
      (== `((,tag ,x^ ,t^) . ,gamma^) gamma)
      (conde
        [(== x x^) (== t t^)]
        [(=/= x x^) (lookupo gamma^ x t tag)]))))

;;; ** be careful with shadowing, and overlapping of application **
(define !-
  (lambda (gamma e t)
    (conde
      [(numbero e) (== 'int t)]
      [(symbolo e)
       (fresh (tag t^ gamma^)
         (lookupo gamma e t^ tag)
         (conde
           [(== 'non-generic tag) (== t^ t)]
           [(== 'generic tag)

            (== gamma gamma^)  ;;; badness: moving this unification after the templateo call causes !-15 to fail instead of !-17
                               ;;; seems like templateo is behaving non-relationally, or I'm confused
            
            (templateo `(,gamma ,t^) `(,gamma^ ,t)) ;; copy the generic template
            
            ]))]
      [(conde
         [(== #t e)]
         [(== #f e)])
       (== 'bool t)]
      [(fresh (e1)
         (== `(zero? ,e1) e)
         (== 'bool t)
         (!- gamma e1 'int))]
      [(fresh (e1)
         (== `(sub1 ,e1) e)
         (== 'int t)
         (!- gamma e1 'int))]      
      [(fresh (x body t1 t2)
         (== `(lambda (,x) ,body) e)
         (== `(-> ,t1 ,t2) t)
         (!- `((non-generic ,x ,t1) . ,gamma) body t2))]
;;;
      [(fresh (x e1 body t1) ; polymorphic let
         (== `(let ((,x ,e1)) ,body) e)
         (!- gamma e1 t1) ; make sure 'e1' has a valid type, regardless of whether 'x' appears in 'body'
         (!- `((generic ,x ,t1) . ,gamma) body t))]
;;;
      [(fresh (e1 e2)
         (== `(* ,e1 ,e2) e)
         (== 'int t)
         (!- gamma e1 'int)
         (!- gamma e2 'int))]      
      [(fresh (e1 e2 t1)
         (== `(,e1 ,e2) e)
         (!- gamma e1 `(-> ,t1 ,t))
         (!- gamma e2 t1))]
      [(fresh (e1 e2 e3)
         (== `(if ,e1 ,e2 ,e3) e)
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

  ;; (test "reduceo-omega"
  ;;   ; diverges, as it should!!    
  ;;   (run 1 (q) (fresh (x y) (reduceo `((lambda (,x) ((,x ,x) (,x ,x))) (lambda (,y) ((,y ,y) (,y ,y)))) q)))
  ;;   'bottom)

  (test "lookupo-1"
    (run* (q) (lookupo `((non-generic x int) (non-generic y bool) (non-generic x bool)) 'x q 'non-generic))
    '(int))

  (test "lookupo-2"
    (run* (q) (fresh (x) (lookupo `((non-generic x int) (non-generic y bool) (non-generic x bool)) x q 'non-generic)))
    '(int bool))

  (test "lookupo-3"
    (run* (q) (lookupo `((non-generic x int) (non-generic y bool) (non-generic x bool)) 'z q 'non-generic))
    '())

  (test "lookupo-4"
    (run 5 (q) (fresh (gamma x t tag) (lookupo gamma x t tag) (== `(,gamma ,x ,t ,tag) q)))
    '((((_.0 _.1 _.2) . _.3) _.1 _.2 _.0)
      ((((_.0 _.1 _.2) (_.0 _.3 _.4) . _.5) _.3 _.4 _.0) : (=/= ((_.1 . _.3))))
      ((((_.0 _.1 _.2) (_.0 _.3 _.4) (_.0 _.5 _.6) . _.7) _.5 _.6 _.0) : (=/= ((_.1 . _.5)) ((_.3 . _.5))))
      ((((_.0 _.1 _.2) (_.0 _.3 _.4) (_.0 _.5 _.6) (_.0 _.7 _.8) . _.9) _.7 _.8 _.0) : (=/= ((_.1 . _.7)) ((_.3 . _.7)) ((_.5 . _.7))))
      ((((_.0 _.1 _.2) (_.0 _.3 _.4) (_.0 _.5 _.6) (_.0 _.7 _.8) (_.0 _.9 _.10) . _.11) _.9 _.10 _.0) : (=/= ((_.1 . _.9)) ((_.3 . _.9)) ((_.5 . _.9)) ((_.7 . _.9))))))

  (test "!-1"
    (run* (q) (!- '() '(lambda (y) y) q))
    '((-> _.0 _.0)))

  (test "!-2"
    (run* (q) (!- '() '((lambda (y) y) (lambda (z) z)) q))
    '((-> _.0 _.0)))

  (test "!-3"
    (run* (q) (!- '() '((lambda (y) y) (lambda (z) (lambda (w) (w z)))) q))
    '((-> _.0 (-> (-> _.0 _.1) _.1))))

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
    '((-> _.0 (-> _.1 _.1))))

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
    '((-> _.0 _.0)))

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

  (test "!-15f"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (if (f 5) (f 6) (f 7))) q))
    '())
  
  (test "!-15g"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (if (f #t) (f 6) (f 7))) q))
    '(int))
  
  (test "!-15"
    (run* (q) (!- '() '(let ((f (lambda (x) x))) (f (zero? (f 5)))) q))
    '(bool))
  
)
