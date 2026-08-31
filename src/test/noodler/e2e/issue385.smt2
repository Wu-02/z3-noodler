(set-info :status sat)
(set-option :produce-models true)
(declare-fun y () String)
(declare-fun x () Real)

; Constrain y to match "0001.XXXXX" where X is a digit
(assert (str.in_re y (re.++ (str.to_re "0001.0000") (re.union (str.to_re "0") (str.to_re "1")) (str.to_re "000"))))

(assert (= x (str.to_real y)))
(assert (= x 1.00001))

(check-sat)
(get-model)
