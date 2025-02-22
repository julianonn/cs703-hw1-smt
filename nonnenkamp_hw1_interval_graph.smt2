(set-logic ALL)
(set-option :produce-models true)

(declare-const au Real)   ; upper bound of interval `a`
(declare-const al Real)   ; lower bound of interval `a`
(declare-const bu Real)   ; ^ for interval b
(declare-const bl Real)   ; and so forth
(declare-const cu Real)
(declare-const cl Real)
(declare-const du Real)
(declare-const dl Real)



; constraint 1:  in a given interval, the lower bound must be strictly less than the upper bound

(assert (< al au))
(assert (< bl bu))
(assert (< cl cu))
(assert (< dl du))


; constraint 2:  determine if each (allegedly) overlapping interval pair has at least one shared element
;
;   define free variables to represent arbitrary values in the intersections of two intervals
;   the intervals a-b, b-c, c-d, & d-a  should have at least one real val in their intersections

(declare-const xab Real)  ; i.e. some val in a \cap b
(declare-const xbc Real)
(declare-const xcd Real)
(declare-const xda Real)

(assert (and (and (< al xab)  (< xab au) ) 
             (and (< bl xab)  (< xab bl) ))) 
(assert (and (and (< bl xbc)  (< xbc bu) ) 
             (and (< cl xbc)  (< xbc cl) ))) 
(assert (and (and (< cl xcd)  (< xcd cu) ) 
             (and (< dl xcd)  (< xcd dl) ))) 
(assert (and (and (< dl xda)  (< xda du) ) 
             (and (< al xda)  (< xda al) ))) 


; constraint 3: make sure no non-overlapping intervals are truly non-overlapping
;   a-c and b-d should not overlap

(assert (or (< au cl) (< cu al)))  ; luckily, we can use existing interval bounds 
(assert (or (< bu dl) (< du bl)))



; finally....
(check-sat)  ; unsat :(
