(set-logic ALL)
(set-info :status sat)
(declare-fun func (String String) Int)

(declare-fun t0 () String)
(declare-fun t1 () String)
(declare-fun t2 () String)

(assert (= (str.len t0) 0))
(assert (not (= (str.len t1) 0)))
(assert (and (>= (func t0 ".") 2) (<= (func t0 ".") 4)))
(assert (and (>= (func t1 "##") 3) (<= (func t1 "##") 5)))

(check-sat)
