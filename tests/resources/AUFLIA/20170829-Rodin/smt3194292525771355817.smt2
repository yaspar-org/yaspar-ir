(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun f (Int Int) Bool)
(declare-fun p () Int)
(declare-fun r () Int)
(declare-fun v () Int)

(assert (! (forall ((x Int)) 
               (=> 
                   (f r x) 
                   (< v x)))
         :named hyp1))
(assert (! (not 
               (<= p (- r 1)))
         :named goal))
(check-sat)
(exit)

