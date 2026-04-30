(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort D 0)
(declare-fun wtp (Int D) Bool)
(declare-fun adr_r () Int)
(declare-fun m () Int)

(assert (! (= adr_r 3)
         :named hyp1))
(assert (! (not 
               (exists ((x D)) 
                   (wtp m x)))
         :named goal))
(check-sat)
(exit)

