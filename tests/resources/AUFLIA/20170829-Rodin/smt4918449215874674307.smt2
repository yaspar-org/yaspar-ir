(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun f (Int Int) Bool)

(assert (! (not 
               (forall ((x Int) (x0 Int)) 
                   (=> 
                       (f x x0) 
                       (and 
                           (<= 0 x) 
                           (<= 0 x0)))))
         :named goal))
(check-sat)
(exit)

