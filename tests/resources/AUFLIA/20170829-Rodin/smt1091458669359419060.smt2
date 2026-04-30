(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unsat)


(assert (! (not 
               (forall ((x Int)) 
                   (= 
                       (= x 1) 
                       (and 
                           (<= 1 x) 
                           (<= x 1)))))
         :named goal))
(check-sat)
(exit)

