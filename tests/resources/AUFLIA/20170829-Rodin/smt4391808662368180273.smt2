(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun f (Int Int) Bool)
(declare-fun n () Int)
(declare-fun v () Int)

(assert (! (not 
               (exists ((x Int)) 
                   (and 
                       (<= 1 x) 
                       (<= x n) 
                       (f x v))))
         :named goal))
(check-sat)
(exit)

