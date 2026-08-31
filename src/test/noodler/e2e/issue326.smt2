(set-logic ALL)
; we cannot solve it, so we pretend the status is unknown
; (set-info :status unknown)
(set-info :status sat)
(declare-const x String)
(assert (= "" (str.replace_re x (re.range "A" (str.at x 0)) (str.from_code 0))))
(check-sat)
