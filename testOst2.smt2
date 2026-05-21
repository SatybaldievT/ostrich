(set-logic QF_SLIA)

(declare-fun x1 () String)
(declare-fun y1 () String)
(declare-fun x2 () String)
(declare-fun y2 () String)

(assert (not (= x1 x2)))
(assert (= (str.++ x1 x1 x1 "A" y1 x1 "B" y1 x1 ) (str.++ x2 x2 x2 "A" y2  x2 "B" y2 x2)))

(check-sat)
(get-model)
