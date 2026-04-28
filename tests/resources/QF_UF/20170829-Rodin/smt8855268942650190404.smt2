(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort Z 0)
(declare-fun circuit () Bool)
(declare-fun flash () Z)
(declare-fun nf () Z)
(declare-fun nf0 () Z)

(assert (! circuit
         :named hyp1))
(assert (! (not 
               (= nf0 nf))
         :named hyp2))
(assert (! (not 
               (or 
                   (= flash nf0) 
                   (= flash nf)))
         :named goal))
(check-sat)
(exit)

