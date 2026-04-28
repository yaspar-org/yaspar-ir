(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun parity (Int Int) Bool)
(declare-fun s () Int)

(assert (! (not 
               (exists ((x Int)) 
                   (parity s x)))
         :named goal))
(check-sat)
(exit)

