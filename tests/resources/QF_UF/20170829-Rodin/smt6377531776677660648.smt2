(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort Z 0)
(declare-fun ab () Bool)
(declare-fun db () Bool)
(declare-fun v () Bool)
(declare-fun r () Z)
(declare-fun s () Z)

(assert (! (=> 
               db 
               (not 
                   ab))
         :named hyp1))
(assert (! v
         :named hyp2))
(assert (! (not 
               (= r s))
         :named hyp3))
(assert (! (not 
               (not 
                   db))
         :named goal))
(check-sat)
(exit)

