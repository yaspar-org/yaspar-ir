(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort N 0)
(declare-fun f (N N) Bool)
(declare-fun n () N)
(declare-fun r () N)

(assert (! (not 
               (= n r))
         :named hyp1))
(assert (! (not 
               (exists ((x N)) 
                   (f n x)))
         :named goal))
(check-sat)
(exit)

