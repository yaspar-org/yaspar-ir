(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test bvsmod edge case
|)
(set-info :category "check")
(set-info :status unsat)
(assert (= (bvsmod (_ bv0 4) (_ bv10 4)) (_ bv10 4)))
(check-sat)
(exit)
