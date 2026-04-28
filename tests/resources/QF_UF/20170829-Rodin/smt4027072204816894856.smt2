(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort D 0)
(declare-fun mOff_red (D) Bool)
(declare-fun red (D) Bool)
(declare-fun d () D)

(assert (! (mOff_red d)
         :named hyp1))
(assert (! (not 
               (red d))
         :named goal))
(check-sat)
(exit)

