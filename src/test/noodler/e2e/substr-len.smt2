(set-logic QF_SLIA)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun s1 () String)
(declare-fun s2 () String)
(declare-fun t () String)
(declare-fun i () Int)

; force 3<=|t|<=4 using int-to-str conversion so that we force main decision procedure and we get to preprocessing
(assert (= (str.from_int i) t))
(assert (<= 100 i))
(assert (<= i 9999))

; we will use generate_equiv preprocessing rule (left sides are same) and because we incorrectly say that the substr lengths are equal, it will create incorrect equation (str.substr s1 1 (str.len t)) = (str.substr s2 1 (str.len t))
(assert (= (str.++ x y) (str.++ (str.substr s1 1 (str.len t)) z)))
(assert (= (str.++ x y) (str.substr s2 1 (str.len t))))

; force |(str.substr s1 1 (str.len t))| < |(str.len t)|
(assert (= (str.len s1) 3))
; force |(str.substr s2 1 (str.len t))| = |(str.len t)|
(assert (= (str.len s2) 5))

(check-sat)
