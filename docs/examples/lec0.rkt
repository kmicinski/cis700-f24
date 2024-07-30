#lang racket

;; my small language of arithmetic,
;; constants, and a single "print"
;; statement (can be nested)
(define (lang? e)
  (match e
    [`(+ ,(? lang? e0) ,(? lang? e1)) #t]
    [`(- ,(? lang? e0) ,(? lang? e1)) #t]
    [`(* ,(? lang? e0) ,(? lang? e1)) #t]
    [`(/ ,(? lang? e0) ,(? lang? e1)) #t]
    [`(print ,(? lang? e))]
    [(? integer? n) #t]))

;; args evaluated left-to-right so this prints (to the console)
;; 1
;; 2
;; 3
'(print (+ (print 1) (print 2)))