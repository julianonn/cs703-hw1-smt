;;  GRAPH G -- Julia Nonnenkamp
;; 
;; I'm too lazy to download cvc5, so I used:  https://cvc5.github.io/app

(set-logic ALL)
(set-option :produce-models true)

; define colors
;; (define-const red Int 0)  ; turns out I don't actually need this
;; (define-const blue Int 1)
;; (define-const green Int 2)


; -----------------------------------
; --------- define vertices ---------
; -----------------------------------

(declare-const p00 Bool) ; v0 has color 0
(declare-const p01 Bool) ; v0 has color 1
(declare-const p02 Bool) ; v0 has color 2

(declare-const p10 Bool) ; v1 has color 0
(declare-const p11 Bool) ; v1 has color 1
(declare-const p12 Bool) ; v1 has color 2

(declare-const p20 Bool) ; v2 has color 0
(declare-const p21 Bool) ; v2 has color 1
(declare-const p22 Bool) ; v2 has color 2

(declare-const p30 Bool) ; v3 has color 0
(declare-const p31 Bool) ; v3 has color 1
(declare-const p32 Bool) ; v3 has color 2


; -----------------------------------
; ----------- CONSTRAINTS -----------
; -----------------------------------

; 1. each vertex can only have 1 color
(define-fun bxor ((a Bool) (b Bool)) Bool   ; boolean xor (native one is for bitvecs?)
    (and (or (and a (not b)) (and (not a) b))))

(assert (bxor p00 (bxor p01 p02))) ; v0 
(assert (bxor p10 (bxor p11 p12))) ; v1
(assert (bxor p20 (bxor p21 p22))) ; v2 
(assert (bxor p30 (bxor p31 p32))) ; v3

; 2. adjacent vertices can't have the same color
; there is definitely some way to do this more efficiently
; but copy and paste is indeed my friend
; 
; Edges:  (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)
(define-fun diff ((px Bool) (py Bool)) Bool 
    (not (and px py)))

(assert (diff p00 p10)) ;  0 --> 1
(assert (diff p01 p11)) 
(assert (diff p02 p12)) 

(assert (diff p00 p20)) ;  0 --> 2
(assert (diff p01 p21)) 
(assert (diff p02 p22)) 

(assert (diff p00 p30)) ;  0 --> 3
(assert (diff p01 p31)) 
(assert (diff p02 p32)) 

(assert (diff p10 p20)) ;  1 --> 2
(assert (diff p11 p21)) 
(assert (diff p12 p22)) 

(assert (diff p10 p30)) ;  1 --> 3
(assert (diff p11 p31)) 
(assert (diff p12 p32)) 

(assert (diff p20 p30)) ;  2 --> 3
(assert (diff p21 p31)) 
(assert (diff p22 p32)) 



; -----------------------------------
; ------------ check sat ------------
; -----------------------------------
(check-sat) ; unsat

