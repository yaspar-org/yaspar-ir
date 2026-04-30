(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* a a) 2))
(assert (= (* b (* b b)) 3))
(check-sat)
(exit)
