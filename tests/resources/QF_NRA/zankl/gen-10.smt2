(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a () Real)
(assert (= (* 4 (* a a)) 2))
(check-sat)
(exit)
