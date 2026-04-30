(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-fun circuit () Bool)
(declare-fun grn_SR () Bool)
(declare-fun org_SR () Bool)
(declare-fun prt () Bool)
(declare-fun rd1 () Bool)
(declare-fun rd2 () Bool)
(declare-fun red_MR () Bool)

(assert (! circuit
         :named hyp1))
(assert (! rd2
         :named hyp2))
(assert (! red_MR
         :named hyp3))
(assert (! (or 
               grn_SR 
               org_SR)
         :named hyp4))
(assert (! (not 
               (or 
                   prt 
                   (not 
                       rd1)))
         :named goal))
(check-sat)
(exit)

