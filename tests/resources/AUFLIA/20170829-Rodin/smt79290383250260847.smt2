(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort D 0)
(declare-sort P 0)
(declare-fun dap (P D) Bool)
(declare-fun mOff_grn (D) Bool)
(declare-fun d () D)

(assert (! (mOff_grn d)
         :named hyp1))
(assert (! (not 
               (exists ((x P)) 
                   (dap x d)))
         :named goal))
(check-sat)
(exit)

