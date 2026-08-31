(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun sb (String) Bool)

(assert (= (sb x) (not (sb y))))
(check-sat)
(get-model)
