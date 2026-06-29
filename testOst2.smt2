(set-logic QF_SLIA)

(declare-fun x1 () String)
(declare-fun y1 () String)
(declare-fun x2 () String)
(declare-fun y2 () String)

(assert (str.suffixof x1 x2))
(assert (< (str.len x1) (str.len x2)))

(assert (str.in_re x1 (re.* (re.union (str.to_re "A") (str.to_re "B")))))
(assert (str.in_re y1 (re.* (re.union (str.to_re "A") (str.to_re "B")))))
(assert (str.in_re x2 (re.* (re.union (str.to_re "A") (str.to_re "B")))))
(assert (str.in_re y2 (re.* (re.union (str.to_re "A") (str.to_re "B")))))
(assert (= (str.++ x1 x1  "A" y1  "B" y1) (str.++ x2 x2 "A" y2  "B" y2)))

(check-sat)
(get-model)
