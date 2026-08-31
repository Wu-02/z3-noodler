(set-logic QF_SLIA)
(set-info :status sat)

(declare-fun suffix!0 () String)
(declare-fun s1 () String)
(declare-fun s2 () String)
(assert (str.suffixof s1 s2))
(assert (< (+ (str.len s1) (str.len s2)) (str.len suffix!0)))

(check-sat)
(get-model)
