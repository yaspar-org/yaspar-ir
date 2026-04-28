(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
(set-info :source |CPAchecker with k-induction on SV-COMP14 program using MathSAT5, submitted by Philipp Wendler, http://cpachecker.sosy-lab.org|)
(set-info :category "industrial")
(set-info :status unsat)


(declare-fun |gcd_test::a@1| () Real)
(declare-fun |gcd_test::b@1| () Real)
(define-fun _7 () Real 0)
(define-fun _140 () Real |gcd_test::b@1|)
(define-fun _144 () Real |gcd_test::a@1|)
(define-fun _180 () Bool (<= _7 _144))
(define-fun _181 () Bool (<= _7 _140))
(define-fun _182 () Bool (and _180 _181))
(define-fun _2 () Bool false)



(assert _182)

(assert _2)
(check-sat)


(exit)
