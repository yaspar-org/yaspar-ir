(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort N 0)
(declare-fun c (N N) Bool)
(declare-fun t () N)

(assert (! (not 
               (exists ((x N)) 
                   (and 
                       (= x t) 
                       (c x t))))
         :named goal))
(check-sat)
(exit)

