(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun g (Int Int) Bool)
(declare-fun r () Int)

(assert (! (not 
               (exists ((x Int)) 
                   (g r x)))
         :named goal))
(check-sat)
(exit)

