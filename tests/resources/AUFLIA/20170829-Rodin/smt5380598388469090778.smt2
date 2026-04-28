(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status sat)

(declare-sort B 0)
(declare-sort R 0)
(declare-fun OCC (B) Bool)
(declare-fun rsrtbl (B R) Bool)
(declare-fun b () B)

(assert (! (OCC b)
         :named hyp1))
(assert (! (not 
               (exists ((x R)) 
                   (rsrtbl b x)))
         :named goal))
(check-sat)
(exit)

