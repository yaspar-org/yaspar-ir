(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(assert (= (_ bv1 1) (bvand (bvnot (_ bv0 1)) (bvand (_ bv1 1) (_ bv1 1)))))
(check-sat)
(exit)
