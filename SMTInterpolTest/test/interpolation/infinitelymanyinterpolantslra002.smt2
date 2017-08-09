(set-option :produce-proofs true)
(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)
(set-logic QF_LRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(assert (! (and (>= (+ (* (- 1) x1) y3 (* (- 1) y2)) 0)
(>= (+ (* (- 1) y3) (* (- 1) y2) (* (- 1) y1)) 0)
(>= (+ (* (- 1) x2) (* (- 1) y3)) 0)
(>= (+ (* 3 x2) (* (- 1) y2)) 0)
(>= x1 0)) :named A))
(assert (! (> (+ (* 2 y3) (* 3 y2) y1) 0) :named B))
(check-sat)
(get-interpolants A B)