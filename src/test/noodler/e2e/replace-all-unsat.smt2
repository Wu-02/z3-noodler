(set-logic QF_SLIA)
(set-info :status unsat)
(declare-const s0 String)
(assert (>= 0 
        (+ 1 (- (str.len s0) (str.len (str.replace_all s0 "-" ""))))))
(check-sat)
