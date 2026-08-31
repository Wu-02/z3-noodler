(set-logic ALL)
(set-info :status sat)
(declare-fun func (String String) Int)

(declare-fun i0 () Int)
(declare-fun i1 () Int)
(declare-fun t0 () String)
(declare-fun t1 () String)
(declare-fun t2 () String)
(declare-fun v0 () Bool)
(declare-fun input_var () String)

(assert (= (str.len t0) 0))
(assert (= input_var (str.++ t0 t1)))
(assert (not (= "" input_var)))
(assert (and (>= (func t0 ".") 2) (<= (func t0 ".") 4)))
(assert (and (>= (func t1 "##") 3) (<= (func t1 "##") 5)))

(check-sat)
