#lang racket
;; Coding lecture notes on intuitionism, illustrating
;; Per Martin-Löf's Intuitionistic Type Theory (ITT) 
;; by way of the Curry-Howard Correspondence
;;
;; We sketch a type system (a variant of the Simply-
;; Typed λ-calculus with sums and products), which is
;; the Curry-Howard analog of IPL. We construct our
;; typing derivations such that well-typed terms
;; correspond to theorems in IPL, and (equivalently)
;; that it is possible to find a well-typed term
;; precisely when a proof (in IPL) exists.

;; We allow any symbol as a base type variable, 'P, 'Q, ...
;; In practice a real language would often have a set
;; of base types such as 'int, 'bool, etc...
;; whose syntactic inhabitants are literals of a specific
;; sort (e.g., 3 and 7 are 'int, #t and #f are 'bool,...)
(define base-type? symbol?)

;; Our type syntax
;; This is the Curry-Howard analog of propositions in IPL
(define (type? t)
  (match t
    ;; An uninhabited type ("False" in IPL)
    ['⊥ #t]
    ;; base type variables, propositional variables in IPL
    [(? base-type? bt) #t]
    ;; arrow types t0 -> t1, logically T0 => T1
    ;; (I.e., implication in IPL)
    [`(,(? type? t0) -> ,(? type? t1)) #t]
    ;; product types, A × B
    ;; these are conjunctions in IPL: A ∧ B
    [`(,(? type? t0) × ,(? type? t1)) #t]
    ;; sum types, disjunctions in IPL: A ∨ B
    [`(,(? type? t0) + ,(? type? t1)) #t]))

;; Valid terms of the simply-typed λ calculus
(define (term? t)
  (match t
    ;; variable reference
    [(? symbol? x) #t]
    ;; construction of pairs
    [`(cons ,(? term? t0) ,(? term? t1)) #t]
    ;; sum introduction, left
    [`(inl ,(? term? t)) #t]
    ;; sum introduction, right
    [`(inr ,(? term? t)) #t]
    ;; case analysis, sum elimination
    [`(case ,(? term? t) ,(? term? t1) ,(? term? t2)) #t]
    ;; product elimination, left
    [`(car ,(? term? t)) #t]
    ;; product elimination, right
    [`(cdr ,(? term? t)) #t]
    ;; lambda, function of a specific simple type
    [`(λ (x : ,(? type? t)) ,(? term? e)) #t]
    ;; assert false -- type to anything
    [`(abort ,(? term? t)) #t]))

;; We define the type rules via natural deduction
;; Our proofs are sequent-based:
;;     Γ ⊢ e : τ, which is read:
;;     "In the environment (in IPL, under the assumptions)
;;      Γ, e has type τ"
;;
;; Notice that this definition is our "trusted computing
;; base:" we are defining which proofs are allowable,
;; forbidding all other constructions.
;;
;; This is a classifier for proofs, saying that the proof
;; pf establishes that in environment Γ, e has type T
(define (types? pf Γ e T)
  ;; a helper function to get the conclusion of a rule
  (define (conclusion pf) (last pf))
  (match pf
    ;; Variable lookup via the environment
    ;;      Γ(x) = T
    ;; Assm -----
    ;;      Γ ⊢ x : T
    [`(Assm ----- \,(? environment? Γ+) ⊢ ,(? symbol? x) : ,(? type? t))
     (and (equal? Γ+ Γ) (equal? (hash-ref Γ x 'none) T t) (equal? x e))]
    ;; Γ ⊢ e0 : A      Γ ⊢ e1 : B
    ;; -------------------------- ×-I
    ;;  Γ ⊢ (cons e0 e1) : A × B
    [`(Cons ,pf-A ,pf-B ----- (cons ,e0 ,e1) : (,A × ,B))
     (and (match (conclusion pf-A) [`(,e0+ : ,A+) (and (equal? e0+ e0) (equal? A A+))])
                 (match (conclusion pf-B) [`(,e1+ : ,B+) (and (equal? e1+ e1) (equal? B B+))])
                 (types? pf-A Γ e0 A)
                 (types? pf-B Γ e1 B))]
    ;;      Γ ⊢ e : A
    ;; -------------------
    ;; Γ ⊢ (inl e) : A ∨ B
    [`(Inl ,pf ----- (inl ,e+) : (,A + ,B))
     (and (match (conclusion pf) [`(,e++ : ,T+) (and (equal? e++ e+ e) (equal? A T+))])
          (match T [`(,A+ + ,B+) (and (equal? A+ A) (equal? B+ B))]))]
    ;;      Γ ⊢ e : B
    ;; -------------------
    ;; Γ ⊢ (inr e) : A ∨ B
    [`(inr ,(? term? t)) #t]
    ;; case analysis, sum elimination
    [`(case ,(? term? t) ,(? term? t1) ,(? term? t2)) #t]
    ;; product elimination, left
    [`(car ,(? term? t)) #t]
    ;; product elimination, right
    [`(cdr ,(? term? t)) #t]
    ;; assert false -- type to anything
    [`(abort ,(? term? t)) #t]))    
    
     
    
    