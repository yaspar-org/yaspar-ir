(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun parity (Int Int) Bool)

(assert (! (not 
               (exists ((x Int) (x0 Int)) 
                   (and 
                       (= x 1) 
                       (= x0 1) 
                       (parity x x0))))
         :named goal))
(check-sat)
(exit)

