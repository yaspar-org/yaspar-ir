(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort D 0)
(declare-fun f (Int D) Bool)
(declare-fun n () Int)
(declare-fun r () Int)

(assert (! (<= r n)
         :named hyp1))
(assert (! (not 
               (exists ((x D)) 
                   (f r x)))
         :named goal))
(check-sat)
(exit)

