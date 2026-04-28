(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :source |Generator: Rodin SMT Plug-in|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "industrial")
(set-info :status unknown)

(declare-sort A 0)
(declare-sort PA 0)
(declare-sort PAA 0)
(declare-sort PZ 0)
(declare-sort PZA 0)
(declare-fun MS (A A PAA) Bool)
(declare-fun MS0 (A PA) Bool)
(declare-fun MS1 (Int A PZA) Bool)
(declare-fun MS2 (Int PZ) Bool)
(declare-fun cnc (PZA PZA PZA) Bool)
(declare-fun dist (A A Int) Bool)
(declare-fun length (PZA Int) Bool)
(declare-fun path (A A PZA) Bool)
(declare-fun reverse (PZA PZA) Bool)
(declare-fun seq (PZA) Bool)
(declare-fun shpath (A A PZA) Bool)
(declare-fun a () PA)
(declare-fun c () PAA)
(declare-fun candidate () PA)
(declare-fun i () Int)
(declare-fun p () PZA)
(declare-fun r () PAA)
(declare-fun x () A)
(declare-fun y () A)

; Elementary Sets axiom (Singleton part)
(assert (forall ((x2074 A) (x2075 A)) 
            (exists ((X PAA)) 
                (and 
                    (MS x2074 x2075 X) 
                    (forall ((y46 A) (y47 A)) 
                        (=> 
                            (MS y46 y47 X) 
                            (and 
                                (= y46 x2074) 
                                (= y47 x2075))))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x2076 A)) 
            (exists ((X0 PA)) 
                (and 
                    (MS0 x2076 X0) 
                    (forall ((y48 A)) 
                        (=> 
                            (MS0 y48 X0) 
                            (= y48 x2076)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x2077 Int)) 
            (exists ((X1 PZ)) 
                (and 
                    (MS2 x2077 X1) 
                    (forall ((y49 Int)) 
                        (=> 
                            (MS2 y49 X1) 
                            (= y49 x2077)))))))
; Elementary Sets axiom (Singleton part)
(assert (forall ((x2078 Int) (x2079 A)) 
            (exists ((X2 PZA)) 
                (and 
                    (MS1 x2078 x2079 X2) 
                    (forall ((y50 Int) (y51 A)) 
                        (=> 
                            (MS1 y50 y51 X2) 
                            (and 
                                (= y50 x2078) 
                                (= y51 x2079))))))))
(assert (! (forall ((x0 A) (x1 A)) 
               (=> 
                   (MS x0 x1 r) 
                   (and 
                       (MS0 x0 a) 
                       (MS0 x1 a))))
         :named hyp1))
(assert (! (not 
               (forall ((x2 A) (x3 A)) 
                   (not 
                       (MS x2 x3 r))))
         :named hyp2))
(assert (! (forall ((x4 A) (x5 A)) 
               (=> 
                   (MS x4 x5 c) 
                   (and 
                       (MS0 x4 a) 
                       (MS0 x5 a))))
         :named hyp3))
(assert (! (forall ((x6 A) (x7 A)) 
               (=> 
                   (MS x6 x7 r) 
                   (MS x6 x7 c)))
         :named hyp4))
(assert (! (forall ((x8 A) (x9 A)) 
               (=> 
                   (exists ((x10 A)) 
                       (and 
                           (MS x8 x10 c) 
                           (MS x10 x9 r))) 
                   (MS x8 x9 c)))
         :named hyp5))
(assert (! (forall ((s PAA)) 
               (=> 
                   (and 
                       (forall ((x11 A) (x12 A)) 
                           (=> 
                               (MS x11 x12 s) 
                               (and 
                                   (MS0 x11 a) 
                                   (MS0 x12 a)))) 
                       (forall ((x13 A) (x14 A)) 
                           (=> 
                               (MS x13 x14 r) 
                               (MS x13 x14 s))) 
                       (forall ((x15 A) (x16 A)) 
                           (=> 
                               (exists ((x17 A)) 
                                   (and 
                                       (MS x15 x17 s) 
                                       (MS x17 x16 r))) 
                               (MS x15 x16 s)))) 
                   (forall ((x18 A) (x19 A)) 
                       (=> 
                           (MS x18 x19 c) 
                           (MS x18 x19 s)))))
         :named hyp6))
(assert (! (forall ((x20 A)) 
               (= 
                   (exists ((x21 A)) 
                       (MS x20 x21 r)) 
                   (MS0 x20 a)))
         :named hyp7))
(assert (! (forall ((x22 A)) 
               (= 
                   (exists ((x23 A)) 
                       (MS x22 x23 c)) 
                   (MS0 x22 a)))
         :named hyp8))
(assert (! (forall ((x24 A)) 
               (=> 
                   (exists ((x25 A)) 
                       (MS x24 x25 r)) 
                   (exists ((x26 A)) 
                       (MS x24 x26 c))))
         :named hyp9))
(assert (! (forall ((x27 A) (x28 A)) 
               (= 
                   (MS x27 x28 c) 
                   (or 
                       (MS x27 x28 r) 
                       (exists ((x29 A)) 
                           (and 
                               (MS x27 x29 c) 
                               (MS x29 x28 r))))))
         :named hyp10))
(assert (! (forall ((x30 A) (y0 A)) 
               (=> 
                   (and 
                       (MS0 x30 a) 
                       (MS0 y0 a)) 
                   (forall ((s0 PZA) (n Int)) 
                       (=> 
                           (and 
                               (<= 0 n) 
                               (< 1 n) 
                               (forall ((x31 Int) (x32 A)) 
                                   (=> 
                                       (MS1 x31 x32 s0) 
                                       (and 
                                           (<= 1 x31) 
                                           (<= x31 n) 
                                           (MS0 x32 a)))) 
                               (forall ((x33 Int) (x34 A) (x35 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x33 x34 s0) 
                                           (MS1 x33 x35 s0)) 
                                       (= x34 x35))) 
                               (forall ((x36 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x36) 
                                           (<= x36 n)) 
                                       (exists ((x37 A)) 
                                           (MS1 x36 x37 s0))))) 
                           (and 
                               (exists ((x38 A) (x39 Int)) 
                                   (and 
                                       (= x39 1) 
                                       (MS1 x39 x38 s0))) 
                               (forall ((x40 Int) (x41 A) (x42 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x40 x41 s0) 
                                           (MS1 x40 x42 s0)) 
                                       (= x41 x42))) 
                               (=> 
                                   (exists ((x43 Int)) 
                                       (and 
                                           (= x43 1) 
                                           (MS1 x43 x30 s0))) 
                                   (and 
                                       (exists ((x44 A)) 
                                           (MS1 n x44 s0)) 
                                       (=> 
                                           (MS1 n y0 s0) 
                                           (forall ((i0 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i0) 
                                                       (<= i0 (- n 1))) 
                                                   (and 
                                                       (exists ((x45 A)) 
                                                           (MS1 i0 x45 s0)) 
                                                       (exists ((x46 A) (x47 Int)) 
                                                           (and 
                                                               (= x47 (+ i0 1)) 
                                                               (MS1 x47 x46 s0))))))))))))))
         :named hyp11))
(assert (! (forall ((s1 PZ) (n0 Int)) 
               (=> 
                   (and 
                       (< 1 n0) 
                       (forall ((x48 Int)) 
                           (=> 
                               (MS2 x48 s1) 
                               (and 
                                   (<= 2 x48) 
                                   (<= x48 n0)))) 
                       (exists ((x49 Int)) 
                           (and 
                               (= x49 2) 
                               (MS2 x49 s1))) 
                       (forall ((i1 Int)) 
                           (=> 
                               (and 
                                   (<= 2 i1) 
                                   (<= i1 (- n0 1)) 
                                   (MS2 i1 s1)) 
                               (exists ((x50 Int)) 
                                   (and 
                                       (= x50 (+ i1 1)) 
                                       (MS2 x50 s1)))))) 
                   (forall ((x51 Int)) 
                       (=> 
                           (and 
                               (<= 2 x51) 
                               (<= x51 n0)) 
                           (MS2 x51 s1)))))
         :named hyp12))
(assert (! (forall ((x52 A) (x53 A)) 
               (=> 
                   (exists ((x54 PZA)) 
                       (path x52 x53 x54)) 
                   (MS x52 x53 c)))
         :named hyp13))
(assert (! (forall ((x55 A) (x56 A)) 
               (=> 
                   (MS x55 x56 c) 
                   (exists ((x57 PZA)) 
                       (path x55 x56 x57))))
         :named hyp14))
(assert (! (forall ((x58 A) (x59 A)) 
               (=> 
                   (and 
                       (MS0 x58 a) 
                       (MS0 x59 a)) 
                   (exists ((x60 PZA)) 
                       (path x58 x59 x60))))
         :named hyp15))
(assert (! (forall ((x61 PZA)) 
               (= 
                   (seq x61) 
                   (exists ((s2 PZA)) 
                       (and 
                           (exists ((n1 Int)) 
                               (and 
                                   (<= 0 n1) 
                                   (forall ((x62 Int) (x63 A)) 
                                       (=> 
                                           (MS1 x62 x63 s2) 
                                           (and 
                                               (<= 1 x62) 
                                               (<= x62 n1)))) 
                                   (forall ((x64 Int) (x65 A) (x66 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x64 x65 s2) 
                                               (MS1 x64 x66 s2)) 
                                           (= x65 x66))) 
                                   (forall ((x67 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x67) 
                                               (<= x67 n1)) 
                                           (exists ((x68 A)) 
                                               (MS1 x67 x68 s2)))))) 
                           (forall ((x69 Int) (x70 A)) 
                               (= 
                                   (MS1 x69 x70 x61) 
                                   (MS1 x69 x70 s2)))))))
         :named hyp16))
(assert (! (forall ((n2 Int) (s3 PZA)) 
               (=> 
                   (and 
                       (<= 0 n2) 
                       (forall ((x71 Int) (x72 A)) 
                           (=> 
                               (MS1 x71 x72 s3) 
                               (and 
                                   (<= 1 x71) 
                                   (<= x71 n2)))) 
                       (forall ((x73 Int) (x74 A) (x75 A)) 
                           (=> 
                               (and 
                                   (MS1 x73 x74 s3) 
                                   (MS1 x73 x75 s3)) 
                               (= x74 x75))) 
                       (forall ((x76 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x76) 
                                   (<= x76 n2)) 
                               (exists ((x77 A)) 
                                   (MS1 x76 x77 s3))))) 
                   (seq s3)))
         :named hyp17))
(assert (! (and 
               (forall ((x78 PZA) (x79 Int)) 
                   (=> 
                       (length x78 x79) 
                       (and 
                           (seq x78) 
                           (<= 0 x79)))) 
               (forall ((x80 PZA) (x81 Int) (x82 Int)) 
                   (=> 
                       (and 
                           (length x80 x81) 
                           (length x80 x82)) 
                       (= x81 x82))) 
               (forall ((x83 PZA)) 
                   (=> 
                       (seq x83) 
                       (exists ((x84 Int)) 
                           (length x83 x84)))))
         :named hyp18))
(assert (! (forall ((n3 Int) (s4 PZA)) 
               (=> 
                   (and 
                       (<= 0 n3) 
                       (forall ((x85 Int) (x86 A)) 
                           (=> 
                               (MS1 x85 x86 s4) 
                               (and 
                                   (<= 1 x85) 
                                   (<= x85 n3)))) 
                       (forall ((x87 Int) (x88 A) (x89 A)) 
                           (=> 
                               (and 
                                   (MS1 x87 x88 s4) 
                                   (MS1 x87 x89 s4)) 
                               (= x88 x89))) 
                       (forall ((x90 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x90) 
                                   (<= x90 n3)) 
                               (exists ((x91 A)) 
                                   (MS1 x90 x91 s4))))) 
                   (length s4 n3)))
         :named hyp19))
(assert (! (forall ((s5 PZA)) 
               (=> 
                   (seq s5) 
                   (and 
                       (forall ((x92 Int) (x93 A)) 
                           (=> 
                               (MS1 x92 x93 s5) 
                               (and 
                                   (<= 1 x92) 
                                   (forall ((x94 Int)) 
                                       (=> 
                                           (length s5 x94) 
                                           (<= x92 x94)))))) 
                       (forall ((x95 Int) (x96 A) (x97 A)) 
                           (=> 
                               (and 
                                   (MS1 x95 x96 s5) 
                                   (MS1 x95 x97 s5)) 
                               (= x96 x97))) 
                       (forall ((x98 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x98) 
                                   (forall ((x99 Int)) 
                                       (=> 
                                           (length s5 x99) 
                                           (<= x98 x99)))) 
                               (exists ((x100 A)) 
                                   (MS1 x98 x100 s5)))))))
         :named hyp20))
(assert (! (forall ((x101 PZA) (x102 PZA) (x103 PZA)) 
               (= 
                   (cnc x101 x102 x103) 
                   (exists ((s10 PZA) (s20 PZA)) 
                       (and 
                           (seq s10) 
                           (seq s20) 
                           (forall ((x104 Int) (x105 A)) 
                               (= 
                                   (MS1 x104 x105 x101) 
                                   (MS1 x104 x105 s10))) 
                           (forall ((x106 Int) (x107 A)) 
                               (= 
                                   (MS1 x106 x107 x102) 
                                   (MS1 x106 x107 s20))) 
                           (forall ((x108 Int) (x109 A)) 
                               (= 
                                   (MS1 x108 x109 x103) 
                                   (or 
                                       (exists ((i2 Int)) 
                                           (and 
                                               (<= 1 i2) 
                                               (forall ((x110 Int)) 
                                                   (=> 
                                                       (length s10 x110) 
                                                       (<= i2 x110))) 
                                               (= x108 i2) 
                                               (MS1 i2 x109 s10))) 
                                       (exists ((i3 Int)) 
                                           (and 
                                               (forall ((x111 Int)) 
                                                   (=> 
                                                       (length s10 x111) 
                                                       (<= (+ x111 1) i3))) 
                                               (forall ((x112 Int) (x113 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s10 x113) 
                                                           (length s20 x112)) 
                                                       (<= i3 (+ x113 x112)))) 
                                               (= x108 i3) 
                                               (exists ((x114 Int)) 
                                                   (and 
                                                       (forall ((x115 Int)) 
                                                           (=> 
                                                               (length s10 x115) 
                                                               (= x114 (- i3 x115)))) 
                                                       (MS1 x114 x109 s20))))))))))))
         :named hyp21))
(assert (! (and 
               (forall ((x116 PZA) (x117 PZA) (x118 PZA)) 
                   (=> 
                       (cnc x116 x117 x118) 
                       (and 
                           (seq x116) 
                           (seq x117) 
                           (seq x118)))) 
               (forall ((x119 PZA) (x120 PZA) (x121 PZA) (x122 PZA)) 
                   (=> 
                       (and 
                           (cnc x119 x120 x121) 
                           (cnc x119 x120 x122)) 
                       (forall ((x123 Int) (x124 A)) 
                           (= 
                               (MS1 x123 x124 x121) 
                               (MS1 x123 x124 x122))))) 
               (forall ((x125 PZA) (x126 PZA)) 
                   (=> 
                       (and 
                           (seq x125) 
                           (seq x126)) 
                       (exists ((x127 PZA)) 
                           (cnc x125 x126 x127)))))
         :named hyp22))
(assert (! (forall ((s11 PZA) (s21 PZA)) 
               (=> 
                   (and 
                       (seq s11) 
                       (seq s21)) 
                   (exists ((x128 PZA) (x129 Int)) 
                       (and 
                           (cnc s11 s21 x128) 
                           (forall ((x130 Int) (x131 Int)) 
                               (=> 
                                   (and 
                                       (length s11 x131) 
                                       (length s21 x130)) 
                                   (= x129 (+ x131 x130)))) 
                           (length x128 x129)))))
         :named hyp23))
(assert (! (forall ((s12 PZA) (s22 PZA)) 
               (=> 
                   (and 
                       (seq s12) 
                       (seq s22)) 
                   (forall ((x132 Int)) 
                       (= 
                           (exists ((x133 A) (x134 PZA)) 
                               (and 
                                   (cnc s12 s22 x134) 
                                   (MS1 x132 x133 x134))) 
                           (and 
                               (<= 1 x132) 
                               (forall ((x135 Int) (x136 Int)) 
                                   (=> 
                                       (and 
                                           (length s12 x136) 
                                           (length s22 x135)) 
                                       (<= x132 (+ x136 x135)))))))))
         :named hyp24))
(assert (! (forall ((s13 PZA) (s23 PZA)) 
               (=> 
                   (and 
                       (seq s13) 
                       (seq s23)) 
                   (forall ((x137 A)) 
                       (= 
                           (exists ((x138 Int) (x139 PZA)) 
                               (and 
                                   (cnc s13 s23 x139) 
                                   (MS1 x138 x137 x139))) 
                           (or 
                               (exists ((x140 Int)) 
                                   (MS1 x140 x137 s13)) 
                               (exists ((x141 Int)) 
                                   (MS1 x141 x137 s23)))))))
         :named hyp25))
(assert (! (forall ((s14 PZA) (s24 PZA) (i4 Int)) 
               (=> 
                   (and 
                       (seq s14) 
                       (seq s24) 
                       (<= 1 i4) 
                       (forall ((x142 Int)) 
                           (=> 
                               (length s14 x142) 
                               (<= i4 x142)))) 
                   (exists ((x143 PZA)) 
                       (and 
                           (cnc s14 s24 x143) 
                           (exists ((x144 A)) 
                               (and 
                                   (MS1 i4 x144 s14) 
                                   (MS1 i4 x144 x143)))))))
         :named hyp26))
(assert (! (forall ((s15 PZA) (s25 PZA) (i5 Int)) 
               (=> 
                   (and 
                       (seq s15) 
                       (seq s25) 
                       (forall ((x145 Int)) 
                           (=> 
                               (length s15 x145) 
                               (<= (+ x145 1) i5))) 
                       (forall ((x146 Int) (x147 Int)) 
                           (=> 
                               (and 
                                   (length s15 x147) 
                                   (length s25 x146)) 
                               (<= i5 (+ x147 x146))))) 
                   (exists ((x148 PZA)) 
                       (and 
                           (cnc s15 s25 x148) 
                           (exists ((x149 A)) 
                               (and 
                                   (exists ((x150 Int)) 
                                       (and 
                                           (forall ((x151 Int)) 
                                               (=> 
                                                   (length s15 x151) 
                                                   (= x150 (- i5 x151)))) 
                                           (MS1 x150 x149 s25))) 
                                   (MS1 i5 x149 x148)))))))
         :named hyp27))
(assert (! (forall ((x152 A) (x153 A)) 
               (not 
                   (and 
                       (MS x152 x153 r) 
                       (= x152 x153))))
         :named hyp28))
(assert (! (and 
               (forall ((x154 A) (x155 A) (x156 Int)) 
                   (=> 
                       (dist x154 x155 x156) 
                       (and 
                           (MS0 x154 a) 
                           (MS0 x155 a) 
                           (<= 0 x156)))) 
               (forall ((x157 A) (x158 A) (x159 Int) (x160 Int)) 
                   (=> 
                       (and 
                           (dist x157 x158 x159) 
                           (dist x157 x158 x160)) 
                       (= x159 x160))) 
               (forall ((x161 A) (x162 A)) 
                   (=> 
                       (and 
                           (MS0 x161 a) 
                           (MS0 x162 a)) 
                       (exists ((x163 Int)) 
                           (dist x161 x162 x163)))))
         :named hyp29))
(assert (! (forall ((x164 A) (y1 A)) 
               (=> 
                   (and 
                       (MS0 x164 a) 
                       (MS0 y1 a)) 
                   (exists ((x165 Int)) 
                       (and 
                           (exists ((x166 PZA)) 
                               (and 
                                   (exists ((x167 A) (x168 A)) 
                                       (and 
                                           (= x167 x164) 
                                           (= x168 y1) 
                                           (path x167 x168 x166))) 
                                   (length x166 x165))) 
                           (forall ((x169 Int)) 
                               (=> 
                                   (exists ((x170 PZA)) 
                                       (and 
                                           (exists ((x171 A) (x172 A)) 
                                               (and 
                                                   (= x171 x164) 
                                                   (= x172 y1) 
                                                   (path x171 x172 x170))) 
                                           (length x170 x169))) 
                                   (<= x165 x169))) 
                           (dist x164 y1 x165)))))
         :named hyp30))
(assert (! (forall ((x173 PZA) (x174 PZA)) 
               (= 
                   (reverse x173 x174) 
                   (exists ((s6 PZA)) 
                       (and 
                           (seq s6) 
                           (forall ((x175 Int) (x176 A)) 
                               (= 
                                   (MS1 x175 x176 x173) 
                                   (MS1 x175 x176 s6))) 
                           (forall ((x177 Int) (x178 A)) 
                               (= 
                                   (MS1 x177 x178 x174) 
                                   (exists ((i6 Int)) 
                                       (and 
                                           (<= 1 i6) 
                                           (forall ((x179 Int)) 
                                               (=> 
                                                   (length s6 x179) 
                                                   (<= i6 x179))) 
                                           (= x177 i6) 
                                           (exists ((x180 Int)) 
                                               (and 
                                                   (forall ((x181 Int)) 
                                                       (=> 
                                                           (length s6 x181) 
                                                           (= x180 (+ (- x181 i6) 1)))) 
                                                   (MS1 x180 x178 s6)))))))))))
         :named hyp31))
(assert (! (and 
               (forall ((x182 PZA) (x183 PZA)) 
                   (=> 
                       (reverse x182 x183) 
                       (and 
                           (seq x182) 
                           (seq x183)))) 
               (forall ((x184 PZA) (x185 PZA) (x186 PZA)) 
                   (=> 
                       (and 
                           (reverse x184 x185) 
                           (reverse x184 x186)) 
                       (forall ((x187 Int) (x188 A)) 
                           (= 
                               (MS1 x187 x188 x185) 
                               (MS1 x187 x188 x186))))) 
               (forall ((x189 PZA)) 
                   (=> 
                       (seq x189) 
                       (exists ((x190 PZA)) 
                           (reverse x189 x190)))))
         :named hyp32))
(assert (! (forall ((s7 PZA)) 
               (=> 
                   (seq s7) 
                   (exists ((x191 PZA) (x192 Int)) 
                       (and 
                           (reverse s7 x191) 
                           (length s7 x192) 
                           (length x191 x192)))))
         :named hyp33))
(assert (! (forall ((s8 PZA)) 
               (=> 
                   (seq s8) 
                   (forall ((x193 A)) 
                       (= 
                           (exists ((x194 Int) (x195 PZA)) 
                               (and 
                                   (reverse s8 x195) 
                                   (MS1 x194 x193 x195))) 
                           (exists ((x196 Int)) 
                               (MS1 x196 x193 s8))))))
         :named hyp34))
(assert (! (forall ((s9 PZA)) 
               (=> 
                   (seq s9) 
                   (exists ((x197 PZA)) 
                       (and 
                           (reverse s9 x197) 
                           (reverse x197 s9)))))
         :named hyp35))
(assert (! (forall ((x198 A) (x199 A)) 
               (=> 
                   (MS x198 x199 r) 
                   (MS x199 x198 r)))
         :named hyp36))
(assert (! (forall ((x200 A) (y2 A) (p0 PZA)) 
               (=> 
                   (path x200 y2 p0) 
                   (exists ((x201 PZA)) 
                       (and 
                           (reverse p0 x201) 
                           (path y2 x200 x201)))))
         :named hyp37))
(assert (! (forall ((x202 A) (y3 A)) 
               (=> 
                   (and 
                       (MS0 x202 a) 
                       (MS0 y3 a)) 
                   (forall ((x203 PZA)) 
                       (= 
                           (exists ((x204 A) (x205 A)) 
                               (and 
                                   (= x204 y3) 
                                   (= x205 x202) 
                                   (path x204 x205 x203))) 
                           (exists ((x206 PZA)) 
                               (and 
                                   (exists ((x207 A) (x208 A)) 
                                       (and 
                                           (= x207 x202) 
                                           (= x208 y3) 
                                           (path x207 x208 x206))) 
                                   (reverse x206 x203)))))))
         :named hyp38))
(assert (! (forall ((x209 A) (y4 A)) 
               (=> 
                   (and 
                       (MS0 x209 a) 
                       (MS0 y4 a)) 
                   (exists ((x210 Int)) 
                       (and 
                           (dist y4 x209 x210) 
                           (dist x209 y4 x210)))))
         :named hyp39))
(assert (! (forall ((x211 A) (x212 A) (x213 PZA)) 
               (= 
                   (shpath x211 x212 x213) 
                   (exists ((x214 A) (y5 A) (p1 PZA)) 
                       (and 
                           (path x214 y5 p1) 
                           (exists ((x215 Int)) 
                               (and 
                                   (length p1 x215) 
                                   (dist x214 y5 x215))) 
                           (= x211 x214) 
                           (= x212 y5) 
                           (forall ((x216 Int) (x217 A)) 
                               (= 
                                   (MS1 x216 x217 x213) 
                                   (MS1 x216 x217 p1)))))))
         :named hyp40))
(assert (! (forall ((x218 A) (y6 A) (p2 PZA)) 
               (=> 
                   (path x218 y6 p2) 
                   (and 
                       (exists ((x219 Int)) 
                           (dist x218 y6 x219)) 
                       (forall ((x220 A) (x221 A) (x222 Int) (x223 Int)) 
                           (=> 
                               (and 
                                   (dist x220 x221 x222) 
                                   (dist x220 x221 x223)) 
                               (= x222 x223))) 
                       (exists ((x224 Int)) 
                           (length p2 x224)) 
                       (forall ((x225 PZA) (x226 Int) (x227 Int)) 
                           (=> 
                               (and 
                                   (length x225 x226) 
                                   (length x225 x227)) 
                               (= x226 x227))))))
         :named hyp41))
(assert (! (forall ((x228 A) (y7 A)) 
               (=> 
                   (and 
                       (MS0 x228 a) 
                       (MS0 y7 a)) 
                   (exists ((x229 PZA)) 
                       (shpath x228 y7 x229))))
         :named hyp42))
(assert (! (forall ((y10 A) (y20 A) (x230 A) (x1100 A) (p3 PZA) (q PZA)) 
               (=> 
                   (and 
                       (MS0 y10 a) 
                       (MS0 y20 a) 
                       (MS0 x230 a) 
                       (MS0 x1100 a) 
                       (path x230 y10 q) 
                       (path y20 x1100 p3) 
                       (MS x1100 x230 r)) 
                   (exists ((x231 PZA)) 
                       (and 
                           (cnc p3 q x231) 
                           (path y20 y10 x231)))))
         :named hyp43))
(assert (! (forall ((x232 A) (y8 A) (p4 PZA) (i7 Int)) 
               (=> 
                   (and 
                       (MS0 x232 a) 
                       (MS0 y8 a) 
                       (path x232 y8 p4) 
                       (<= 2 i7) 
                       (forall ((x233 Int)) 
                           (=> 
                               (length p4 x233) 
                               (<= i7 (- x233 1))))) 
                   (exists ((x234 A) (x235 PZA)) 
                       (and 
                           (MS1 i7 x234 p4) 
                           (forall ((x236 Int) (x237 A)) 
                               (= 
                                   (MS1 x236 x237 x235) 
                                   (and 
                                       (MS1 x236 x237 p4) 
                                       (<= 1 x236) 
                                       (<= x236 i7)))) 
                           (path x232 x234 x235)))))
         :named hyp44))
(assert (! (forall ((x238 A) (y21 A) (p5 PZA)) 
               (=> 
                   (and 
                       (MS0 x238 a) 
                       (MS0 y21 a) 
                       (path x238 y21 p5) 
                       (forall ((x239 Int)) 
                           (=> 
                               (length p5 x239) 
                               (<= 3 x239)))) 
                   (exists ((x240 A) (x241 PZA)) 
                       (and 
                           (exists ((x242 PZA)) 
                               (and 
                                   (reverse p5 x242) 
                                   (exists ((x243 Int)) 
                                       (and 
                                           (forall ((x244 Int)) 
                                               (=> 
                                                   (length p5 x244) 
                                                   (= x243 (- x244 1)))) 
                                           (MS1 x243 x240 x242))))) 
                           (forall ((x245 Int) (x246 A)) 
                               (= 
                                   (MS1 x245 x246 x241) 
                                   (and 
                                       (exists ((x247 PZA)) 
                                           (and 
                                               (reverse p5 x247) 
                                               (MS1 x245 x246 x247))) 
                                       (<= 1 x245) 
                                       (forall ((x248 Int)) 
                                           (=> 
                                               (length p5 x248) 
                                               (<= x245 (- x248 1))))))) 
                           (path y21 x240 x241)))))
         :named hyp45))
(assert (! (forall ((x249 A) (x250 A) (x251 PZA)) 
               (= 
                   (path x249 x250 x251) 
                   (exists ((x252 A) (y9 A) (p6 PZA)) 
                       (and 
                           (MS0 x252 a) 
                           (MS0 y9 a) 
                           (exists ((n4 Int)) 
                               (and 
                                   (<= 0 n4) 
                                   (< 1 n4) 
                                   (forall ((x253 Int) (x254 A)) 
                                       (=> 
                                           (MS1 x253 x254 p6) 
                                           (and 
                                               (<= 1 x253) 
                                               (<= x253 n4) 
                                               (MS0 x254 a)))) 
                                   (forall ((x255 Int) (x256 A) (x257 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x255 x256 p6) 
                                               (MS1 x255 x257 p6)) 
                                           (= x256 x257))) 
                                   (forall ((x258 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x258) 
                                               (<= x258 n4)) 
                                           (exists ((x259 A)) 
                                               (MS1 x258 x259 p6)))) 
                                   (exists ((x260 Int)) 
                                       (and 
                                           (= x260 1) 
                                           (MS1 x260 x252 p6))) 
                                   (MS1 n4 y9 p6) 
                                   (forall ((i8 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 i8) 
                                               (<= i8 (- n4 1))) 
                                           (exists ((x261 A) (x262 A)) 
                                               (and 
                                                   (MS1 i8 x261 p6) 
                                                   (exists ((x263 Int)) 
                                                       (and 
                                                           (= x263 (+ i8 1)) 
                                                           (MS1 x263 x262 p6))) 
                                                   (MS x261 x262 r))))))) 
                           (= x249 x252) 
                           (= x250 y9) 
                           (forall ((x264 Int) (x265 A)) 
                               (= 
                                   (MS1 x264 x265 x251) 
                                   (MS1 x264 x265 p6)))))))
         :named hyp46))
(assert (! (forall ((x266 A)) 
               (= 
                   (MS0 x266 candidate) 
                   (exists ((z A)) 
                       (and 
                           (MS0 z a) 
                           (forall ((x267 A) (y11 A)) 
                               (=> 
                                   (and 
                                       (MS0 x267 a) 
                                       (not 
                                           (= x267 z)) 
                                       (MS0 y11 a) 
                                       (not 
                                           (= y11 z)) 
                                       (not 
                                           (= x267 y11))) 
                                   (exists ((p7 PZA)) 
                                       (and 
                                           (exists ((x268 A) (x269 A)) 
                                               (and 
                                                   (= x268 x267) 
                                                   (= x269 y11) 
                                                   (path x268 x269 p7))) 
                                           (not 
                                               (exists ((x270 Int)) 
                                                   (MS1 x270 z p7))))))) 
                           (= x266 z)))))
         :named hyp47))
(assert (! (forall ((u A)) 
               (=> 
                   (MS0 u candidate) 
                   (forall ((x271 A) (x272 A)) 
                       (=> 
                           (and 
                               (MS0 x271 a) 
                               (not 
                                   (= x271 u)) 
                               (MS0 x272 a) 
                               (not 
                                   (= x272 u)) 
                               (not 
                                   (= x271 x272))) 
                           (exists ((x273 A) (y12 A) (p8 PZA)) 
                               (and 
                                   (MS0 x273 a) 
                                   (not 
                                       (= x273 u)) 
                                   (MS0 y12 a) 
                                   (not 
                                       (= y12 u)) 
                                   (not 
                                       (= x273 y12)) 
                                   (exists ((n5 Int)) 
                                       (and 
                                           (<= 0 n5) 
                                           (< 1 n5) 
                                           (forall ((x274 Int) (x275 A)) 
                                               (=> 
                                                   (MS1 x274 x275 p8) 
                                                   (and 
                                                       (<= 1 x274) 
                                                       (<= x274 n5) 
                                                       (MS0 x275 a) 
                                                       (not 
                                                           (= x275 u))))) 
                                           (forall ((x276 Int) (x277 A) (x278 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x276 x277 p8) 
                                                       (MS1 x276 x278 p8)) 
                                                   (= x277 x278))) 
                                           (forall ((x279 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x279) 
                                                       (<= x279 n5)) 
                                                   (exists ((x280 A)) 
                                                       (MS1 x279 x280 p8)))) 
                                           (exists ((x281 Int)) 
                                               (and 
                                                   (= x281 1) 
                                                   (MS1 x281 x273 p8))) 
                                           (MS1 n5 y12 p8) 
                                           (forall ((i9 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i9) 
                                                       (<= i9 (- n5 1))) 
                                                   (exists ((x282 A) (x283 A)) 
                                                       (and 
                                                           (MS1 i9 x282 p8) 
                                                           (exists ((x284 Int)) 
                                                               (and 
                                                                   (= x284 (+ i9 1)) 
                                                                   (MS1 x284 x283 p8))) 
                                                           (MS x282 x283 r))))))) 
                                   (= x271 x273) 
                                   (= x272 y12)))))))
         :named hyp48))
(assert (! (forall ((s16 PZA) (s26 PZA)) 
               (=> 
                   (and 
                       (seq s16) 
                       (seq s26)) 
                   (and 
                       (exists ((x285 Int)) 
                           (length s16 x285)) 
                       (forall ((x286 PZA) (x287 Int) (x288 Int)) 
                           (=> 
                               (and 
                                   (length x286 x287) 
                                   (length x286 x288)) 
                               (= x287 x288))) 
                       (forall ((i10 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i10) 
                                   (forall ((x289 Int)) 
                                       (=> 
                                           (length s16 x289) 
                                           (<= i10 x289)))) 
                               (and 
                                   (exists ((x290 A)) 
                                       (MS1 i10 x290 s16)) 
                                   (forall ((x291 Int) (x292 A) (x293 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x291 x292 s16) 
                                               (MS1 x291 x293 s16)) 
                                           (= x292 x293)))))) 
                       (exists ((x294 Int)) 
                           (length s26 x294)) 
                       (forall ((i11 Int)) 
                           (=> 
                               (and 
                                   (forall ((x295 Int)) 
                                       (=> 
                                           (length s16 x295) 
                                           (<= (+ x295 1) i11))) 
                                   (forall ((x296 Int) (x297 Int)) 
                                       (=> 
                                           (and 
                                               (length s16 x297) 
                                               (length s26 x296)) 
                                           (<= i11 (+ x297 x296))))) 
                               (and 
                                   (exists ((x298 A) (x299 Int)) 
                                       (and 
                                           (forall ((x300 Int)) 
                                               (=> 
                                                   (length s16 x300) 
                                                   (= x299 (- i11 x300)))) 
                                           (MS1 x299 x298 s26))) 
                                   (forall ((x301 Int) (x302 A) (x303 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x301 x302 s26) 
                                               (MS1 x301 x303 s26)) 
                                           (= x302 x303)))))))))
         :named hyp49))
(assert (! (forall ((s17 PZA)) 
               (=> 
                   (seq s17) 
                   (and 
                       (exists ((x304 Int)) 
                           (length s17 x304)) 
                       (forall ((x305 PZA) (x306 Int) (x307 Int)) 
                           (=> 
                               (and 
                                   (length x305 x306) 
                                   (length x305 x307)) 
                               (= x306 x307))) 
                       (forall ((i12 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i12) 
                                   (forall ((x308 Int)) 
                                       (=> 
                                           (length s17 x308) 
                                           (<= i12 x308)))) 
                               (and 
                                   (exists ((x309 A) (x310 Int)) 
                                       (and 
                                           (forall ((x311 Int)) 
                                               (=> 
                                                   (length s17 x311) 
                                                   (= x310 (+ (- x311 i12) 1)))) 
                                           (MS1 x310 x309 s17))) 
                                   (forall ((x312 Int) (x313 A) (x314 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x312 x313 s17) 
                                               (MS1 x312 x314 s17)) 
                                           (= x313 x314)))))))))
         :named hyp50))
(assert (! (forall ((x315 A) (y13 A) (p9 PZA) (i13 Int)) 
               (=> 
                   (and 
                       (MS0 x315 a) 
                       (MS0 y13 a) 
                       (seq p9) 
                       (shpath x315 y13 p9) 
                       (exists ((x316 A)) 
                           (MS1 i13 x316 p9)) 
                       (not 
                           (= i13 1)) 
                       (not 
                           (length p9 i13))) 
                   (exists ((x317 A) (x318 PZA)) 
                       (and 
                           (MS1 i13 x317 p9) 
                           (forall ((x319 Int) (x320 A)) 
                               (= 
                                   (MS1 x319 x320 x318) 
                                   (and 
                                       (MS1 x319 x320 p9) 
                                       (<= 1 x319) 
                                       (<= x319 i13)))) 
                           (shpath x315 x317 x318)))))
         :named hyp51))
(assert (! (forall ((x321 A) (y14 A) (p10 PZA) (i14 Int)) 
               (=> 
                   (and 
                       (MS0 x321 a) 
                       (MS0 y14 a) 
                       (seq p10) 
                       (shpath x321 y14 p10) 
                       (exists ((x322 A)) 
                           (MS1 i14 x322 p10)) 
                       (not 
                           (= i14 1)) 
                       (not 
                           (length p10 i14))) 
                   (and 
                       (exists ((x323 A)) 
                           (and 
                               (MS1 i14 x323 p10) 
                               (dist x321 x323 i14))) 
                       (exists ((x324 A) (x325 Int)) 
                           (and 
                               (exists ((x326 Int)) 
                                   (and 
                                       (= x326 (+ i14 1)) 
                                       (MS1 x326 x324 p10))) 
                               (= x325 (+ i14 1)) 
                               (dist x321 x324 x325))) 
                       (exists ((x327 A) (x328 A)) 
                           (and 
                               (MS1 i14 x327 p10) 
                               (exists ((x329 Int)) 
                                   (and 
                                       (= x329 (+ i14 1)) 
                                       (MS1 x329 x328 p10))) 
                               (MS x327 x328 r))))))
         :named hyp52))
(assert (! (forall ((x330 A) (y15 A) (p11 PZA) (z0 A)) 
               (=> 
                   (and 
                       (MS0 x330 a) 
                       (MS0 y15 a) 
                       (seq p11) 
                       (shpath x330 y15 p11) 
                       (exists ((x331 Int)) 
                           (MS1 x331 z0 p11)) 
                       (not 
                           (= z0 x330)) 
                       (not 
                           (= z0 y15))) 
                   (exists ((t A)) 
                       (and 
                           (MS0 t a) 
                           (forall ((x332 Int) (x333 Int)) 
                               (=> 
                                   (and 
                                       (dist x330 z0 x333) 
                                       (dist x330 t x332)) 
                                   (< x333 x332))) 
                           (MS z0 t r)))))
         :named hyp53))
(assert (! (forall ((x334 A) (y16 A) (z1 A)) 
               (=> 
                   (and 
                       (MS0 x334 a) 
                       (MS0 y16 a) 
                       (MS0 z1 a) 
                       (not 
                           (= z1 x334)) 
                       (not 
                           (= z1 y16)) 
                       (forall ((t0 A)) 
                           (=> 
                               (and 
                                   (MS0 t0 a) 
                                   (MS z1 t0 r)) 
                               (forall ((x335 Int) (x336 Int)) 
                                   (=> 
                                       (and 
                                           (dist x334 t0 x336) 
                                           (dist x334 z1 x335)) 
                                       (<= x336 x335)))))) 
                   (exists ((q0 PZA)) 
                       (and 
                           (path x334 y16 q0) 
                           (not 
                               (exists ((x337 Int)) 
                                   (MS1 x337 z1 q0)))))))
         :named hyp54))
(assert (! (forall ((x338 A) (x339 A)) 
               (=> 
                   (and 
                       (MS0 x338 a) 
                       (MS0 x339 a)) 
                   (MS x338 x339 c)))
         :named hyp55))
(assert (! (not 
               (forall ((x340 A)) 
                   (MS0 x340 a)))
         :named hyp56))
(assert (! (forall ((s18 PZA) (s27 PZA) (b PA)) 
               (=> 
                   (and 
                       (seq s18) 
                       (seq s27) 
                       (forall ((x341 A)) 
                           (=> 
                               (exists ((x342 Int)) 
                                   (MS1 x342 x341 s18)) 
                               (MS0 x341 b))) 
                       (forall ((x343 A)) 
                           (=> 
                               (exists ((x344 Int)) 
                                   (MS1 x344 x343 s27)) 
                               (MS0 x343 b)))) 
                   (and 
                       (forall ((x345 Int) (x346 A)) 
                           (=> 
                               (exists ((x347 PZA)) 
                                   (and 
                                       (cnc s18 s27 x347) 
                                       (MS1 x345 x346 x347))) 
                               (and 
                                   (<= 1 x345) 
                                   (forall ((x348 Int) (x349 Int)) 
                                       (=> 
                                           (and 
                                               (length s18 x349) 
                                               (length s27 x348)) 
                                           (<= x345 (+ x349 x348)))) 
                                   (MS0 x346 b)))) 
                       (forall ((x350 Int) (x351 A) (x352 A)) 
                           (=> 
                               (and 
                                   (exists ((x353 PZA)) 
                                       (and 
                                           (cnc s18 s27 x353) 
                                           (MS1 x350 x351 x353))) 
                                   (exists ((x354 PZA)) 
                                       (and 
                                           (cnc s18 s27 x354) 
                                           (MS1 x350 x352 x354)))) 
                               (= x351 x352))) 
                       (forall ((x355 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x355) 
                                   (forall ((x356 Int) (x357 Int)) 
                                       (=> 
                                           (and 
                                               (length s18 x357) 
                                               (length s27 x356)) 
                                           (<= x355 (+ x357 x356))))) 
                               (exists ((x358 A) (x359 PZA)) 
                                   (and 
                                       (cnc s18 s27 x359) 
                                       (MS1 x355 x358 x359))))))))
         :named hyp57))
(assert (! (forall ((x360 A) (x361 A) (x362 PZA)) 
               (= 
                   (path x360 x361 x362) 
                   (exists ((x363 A) (y17 A) (p12 PZA)) 
                       (and 
                           (seq p12) 
                           (forall ((x364 A)) 
                               (=> 
                                   (exists ((x365 Int)) 
                                       (MS1 x365 x364 p12)) 
                                   (MS0 x364 a))) 
                           (forall ((x366 Int)) 
                               (=> 
                                   (length p12 x366) 
                                   (< 1 x366))) 
                           (exists ((x367 Int)) 
                               (and 
                                   (= x367 1) 
                                   (MS1 x367 x363 p12))) 
                           (exists ((x368 Int)) 
                               (and 
                                   (length p12 x368) 
                                   (MS1 x368 y17 p12))) 
                           (forall ((i15 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i15) 
                                       (forall ((x369 Int)) 
                                           (=> 
                                               (length p12 x369) 
                                               (<= i15 (- x369 1))))) 
                                   (exists ((x370 A) (x371 A)) 
                                       (and 
                                           (MS1 i15 x370 p12) 
                                           (exists ((x372 Int)) 
                                               (and 
                                                   (= x372 (+ i15 1)) 
                                                   (MS1 x372 x371 p12))) 
                                           (MS x370 x371 r))))) 
                           (= x360 x363) 
                           (= x361 y17) 
                           (forall ((x373 Int) (x374 A)) 
                               (= 
                                   (MS1 x373 x374 x362) 
                                   (MS1 x373 x374 p12)))))))
         :named hyp58))
(assert (! (forall ((x375 A) (y18 A) (p13 PZA)) 
               (=> 
                   (and 
                       (seq p13) 
                       (forall ((x376 A)) 
                           (=> 
                               (exists ((x377 Int)) 
                                   (MS1 x377 x376 p13)) 
                               (MS0 x376 a)))) 
                   (and 
                       (exists ((x378 Int)) 
                           (length p13 x378)) 
                       (forall ((x379 PZA) (x380 Int) (x381 Int)) 
                           (=> 
                               (and 
                                   (length x379 x380) 
                                   (length x379 x381)) 
                               (= x380 x381))) 
                       (=> 
                           (forall ((x382 Int)) 
                               (=> 
                                   (length p13 x382) 
                                   (< 1 x382))) 
                           (and 
                               (exists ((x383 A) (x384 Int)) 
                                   (and 
                                       (= x384 1) 
                                       (MS1 x384 x383 p13))) 
                               (forall ((x385 Int) (x386 A) (x387 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x385 x386 p13) 
                                           (MS1 x385 x387 p13)) 
                                       (= x386 x387))) 
                               (=> 
                                   (exists ((x388 Int)) 
                                       (and 
                                           (= x388 1) 
                                           (MS1 x388 x375 p13))) 
                                   (and 
                                       (exists ((x389 A) (x390 Int)) 
                                           (and 
                                               (length p13 x390) 
                                               (MS1 x390 x389 p13))) 
                                       (=> 
                                           (exists ((x391 Int)) 
                                               (and 
                                                   (length p13 x391) 
                                                   (MS1 x391 y18 p13))) 
                                           (forall ((i16 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i16) 
                                                       (forall ((x392 Int)) 
                                                           (=> 
                                                               (length p13 x392) 
                                                               (<= i16 (- x392 1))))) 
                                                   (and 
                                                       (exists ((x393 A)) 
                                                           (MS1 i16 x393 p13)) 
                                                       (exists ((x394 A) (x395 Int)) 
                                                           (and 
                                                               (= x395 (+ i16 1)) 
                                                               (MS1 x395 x394 p13))))))))))))))
         :named hyp59))
(assert (! (shpath x y p)
         :named hyp60))
(assert (! (and 
               (forall ((x396 PZA) (x397 Int)) 
                   (=> 
                       (length x396 x397) 
                       (and 
                           (exists ((s19 PZA)) 
                               (and 
                                   (exists ((n6 Int)) 
                                       (and 
                                           (<= 0 n6) 
                                           (forall ((x398 Int) (x399 A)) 
                                               (=> 
                                                   (MS1 x398 x399 s19) 
                                                   (and 
                                                       (<= 1 x398) 
                                                       (<= x398 n6)))) 
                                           (forall ((x400 Int) (x401 A) (x402 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x400 x401 s19) 
                                                       (MS1 x400 x402 s19)) 
                                                   (= x401 x402))) 
                                           (forall ((x403 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x403) 
                                                       (<= x403 n6)) 
                                                   (exists ((x404 A)) 
                                                       (MS1 x403 x404 s19)))))) 
                                   (forall ((x405 Int) (x406 A)) 
                                       (= 
                                           (MS1 x405 x406 x396) 
                                           (MS1 x405 x406 s19))))) 
                           (<= 0 x397)))) 
               (forall ((x407 PZA) (x408 Int) (x409 Int)) 
                   (=> 
                       (and 
                           (length x407 x408) 
                           (length x407 x409)) 
                       (= x408 x409))) 
               (forall ((x410 PZA)) 
                   (=> 
                       (exists ((s28 PZA)) 
                           (and 
                               (exists ((n7 Int)) 
                                   (and 
                                       (<= 0 n7) 
                                       (forall ((x411 Int) (x412 A)) 
                                           (=> 
                                               (MS1 x411 x412 s28) 
                                               (and 
                                                   (<= 1 x411) 
                                                   (<= x411 n7)))) 
                                       (forall ((x413 Int) (x414 A) (x415 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x413 x414 s28) 
                                                   (MS1 x413 x415 s28)) 
                                               (= x414 x415))) 
                                       (forall ((x416 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x416) 
                                                   (<= x416 n7)) 
                                               (exists ((x417 A)) 
                                                   (MS1 x416 x417 s28)))))) 
                               (forall ((x418 Int) (x419 A)) 
                                   (= 
                                       (MS1 x418 x419 x410) 
                                       (MS1 x418 x419 s28))))) 
                       (exists ((x420 Int)) 
                           (length x410 x420)))))
         :named hyp61))
(assert (! (and 
               (forall ((x421 PZA) (x422 PZA) (x423 PZA)) 
                   (=> 
                       (cnc x421 x422 x423) 
                       (and 
                           (exists ((s29 PZA)) 
                               (and 
                                   (exists ((n8 Int)) 
                                       (and 
                                           (<= 0 n8) 
                                           (forall ((x424 Int) (x425 A)) 
                                               (=> 
                                                   (MS1 x424 x425 s29) 
                                                   (and 
                                                       (<= 1 x424) 
                                                       (<= x424 n8)))) 
                                           (forall ((x426 Int) (x427 A) (x428 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x426 x427 s29) 
                                                       (MS1 x426 x428 s29)) 
                                                   (= x427 x428))) 
                                           (forall ((x429 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x429) 
                                                       (<= x429 n8)) 
                                                   (exists ((x430 A)) 
                                                       (MS1 x429 x430 s29)))))) 
                                   (forall ((x431 Int) (x432 A)) 
                                       (= 
                                           (MS1 x431 x432 x421) 
                                           (MS1 x431 x432 s29))))) 
                           (exists ((s30 PZA)) 
                               (and 
                                   (exists ((n9 Int)) 
                                       (and 
                                           (<= 0 n9) 
                                           (forall ((x433 Int) (x434 A)) 
                                               (=> 
                                                   (MS1 x433 x434 s30) 
                                                   (and 
                                                       (<= 1 x433) 
                                                       (<= x433 n9)))) 
                                           (forall ((x435 Int) (x436 A) (x437 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x435 x436 s30) 
                                                       (MS1 x435 x437 s30)) 
                                                   (= x436 x437))) 
                                           (forall ((x438 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x438) 
                                                       (<= x438 n9)) 
                                                   (exists ((x439 A)) 
                                                       (MS1 x438 x439 s30)))))) 
                                   (forall ((x440 Int) (x441 A)) 
                                       (= 
                                           (MS1 x440 x441 x422) 
                                           (MS1 x440 x441 s30))))) 
                           (exists ((s31 PZA)) 
                               (and 
                                   (exists ((n10 Int)) 
                                       (and 
                                           (<= 0 n10) 
                                           (forall ((x442 Int) (x443 A)) 
                                               (=> 
                                                   (MS1 x442 x443 s31) 
                                                   (and 
                                                       (<= 1 x442) 
                                                       (<= x442 n10)))) 
                                           (forall ((x444 Int) (x445 A) (x446 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x444 x445 s31) 
                                                       (MS1 x444 x446 s31)) 
                                                   (= x445 x446))) 
                                           (forall ((x447 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x447) 
                                                       (<= x447 n10)) 
                                                   (exists ((x448 A)) 
                                                       (MS1 x447 x448 s31)))))) 
                                   (forall ((x449 Int) (x450 A)) 
                                       (= 
                                           (MS1 x449 x450 x423) 
                                           (MS1 x449 x450 s31)))))))) 
               (forall ((x451 PZA) (x452 PZA) (x453 PZA) (x454 PZA)) 
                   (=> 
                       (and 
                           (cnc x451 x452 x453) 
                           (cnc x451 x452 x454)) 
                       (forall ((x455 Int) (x456 A)) 
                           (= 
                               (MS1 x455 x456 x453) 
                               (MS1 x455 x456 x454))))) 
               (forall ((x457 PZA) (x458 PZA)) 
                   (=> 
                       (and 
                           (exists ((s32 PZA)) 
                               (and 
                                   (exists ((n11 Int)) 
                                       (and 
                                           (<= 0 n11) 
                                           (forall ((x459 Int) (x460 A)) 
                                               (=> 
                                                   (MS1 x459 x460 s32) 
                                                   (and 
                                                       (<= 1 x459) 
                                                       (<= x459 n11)))) 
                                           (forall ((x461 Int) (x462 A) (x463 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x461 x462 s32) 
                                                       (MS1 x461 x463 s32)) 
                                                   (= x462 x463))) 
                                           (forall ((x464 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x464) 
                                                       (<= x464 n11)) 
                                                   (exists ((x465 A)) 
                                                       (MS1 x464 x465 s32)))))) 
                                   (forall ((x466 Int) (x467 A)) 
                                       (= 
                                           (MS1 x466 x467 x457) 
                                           (MS1 x466 x467 s32))))) 
                           (exists ((s33 PZA)) 
                               (and 
                                   (exists ((n12 Int)) 
                                       (and 
                                           (<= 0 n12) 
                                           (forall ((x468 Int) (x469 A)) 
                                               (=> 
                                                   (MS1 x468 x469 s33) 
                                                   (and 
                                                       (<= 1 x468) 
                                                       (<= x468 n12)))) 
                                           (forall ((x470 Int) (x471 A) (x472 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x470 x471 s33) 
                                                       (MS1 x470 x472 s33)) 
                                                   (= x471 x472))) 
                                           (forall ((x473 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x473) 
                                                       (<= x473 n12)) 
                                                   (exists ((x474 A)) 
                                                       (MS1 x473 x474 s33)))))) 
                                   (forall ((x475 Int) (x476 A)) 
                                       (= 
                                           (MS1 x475 x476 x458) 
                                           (MS1 x475 x476 s33)))))) 
                       (exists ((x477 PZA)) 
                           (cnc x457 x458 x477)))))
         :named hyp62))
(assert (! (and 
               (forall ((x478 PZA) (x479 PZA)) 
                   (=> 
                       (reverse x478 x479) 
                       (and 
                           (exists ((s34 PZA)) 
                               (and 
                                   (exists ((n13 Int)) 
                                       (and 
                                           (<= 0 n13) 
                                           (forall ((x480 Int) (x481 A)) 
                                               (=> 
                                                   (MS1 x480 x481 s34) 
                                                   (and 
                                                       (<= 1 x480) 
                                                       (<= x480 n13)))) 
                                           (forall ((x482 Int) (x483 A) (x484 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x482 x483 s34) 
                                                       (MS1 x482 x484 s34)) 
                                                   (= x483 x484))) 
                                           (forall ((x485 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x485) 
                                                       (<= x485 n13)) 
                                                   (exists ((x486 A)) 
                                                       (MS1 x485 x486 s34)))))) 
                                   (forall ((x487 Int) (x488 A)) 
                                       (= 
                                           (MS1 x487 x488 x478) 
                                           (MS1 x487 x488 s34))))) 
                           (exists ((s35 PZA)) 
                               (and 
                                   (exists ((n14 Int)) 
                                       (and 
                                           (<= 0 n14) 
                                           (forall ((x489 Int) (x490 A)) 
                                               (=> 
                                                   (MS1 x489 x490 s35) 
                                                   (and 
                                                       (<= 1 x489) 
                                                       (<= x489 n14)))) 
                                           (forall ((x491 Int) (x492 A) (x493 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x491 x492 s35) 
                                                       (MS1 x491 x493 s35)) 
                                                   (= x492 x493))) 
                                           (forall ((x494 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x494) 
                                                       (<= x494 n14)) 
                                                   (exists ((x495 A)) 
                                                       (MS1 x494 x495 s35)))))) 
                                   (forall ((x496 Int) (x497 A)) 
                                       (= 
                                           (MS1 x496 x497 x479) 
                                           (MS1 x496 x497 s35)))))))) 
               (forall ((x498 PZA) (x499 PZA) (x500 PZA)) 
                   (=> 
                       (and 
                           (reverse x498 x499) 
                           (reverse x498 x500)) 
                       (forall ((x501 Int) (x502 A)) 
                           (= 
                               (MS1 x501 x502 x499) 
                               (MS1 x501 x502 x500))))) 
               (forall ((x503 PZA)) 
                   (=> 
                       (exists ((s36 PZA)) 
                           (and 
                               (exists ((n15 Int)) 
                                   (and 
                                       (<= 0 n15) 
                                       (forall ((x504 Int) (x505 A)) 
                                           (=> 
                                               (MS1 x504 x505 s36) 
                                               (and 
                                                   (<= 1 x504) 
                                                   (<= x504 n15)))) 
                                       (forall ((x506 Int) (x507 A) (x508 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x506 x507 s36) 
                                                   (MS1 x506 x508 s36)) 
                                               (= x507 x508))) 
                                       (forall ((x509 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x509) 
                                                   (<= x509 n15)) 
                                               (exists ((x510 A)) 
                                                   (MS1 x509 x510 s36)))))) 
                               (forall ((x511 Int) (x512 A)) 
                                   (= 
                                       (MS1 x511 x512 x503) 
                                       (MS1 x511 x512 s36))))) 
                       (exists ((x513 PZA)) 
                           (reverse x503 x513)))))
         :named hyp63))
(assert (! (forall ((n16 Int) (s37 PZA)) 
               (=> 
                   (and 
                       (<= 0 n16) 
                       (forall ((x514 Int) (x515 A)) 
                           (=> 
                               (MS1 x514 x515 s37) 
                               (and 
                                   (<= 1 x514) 
                                   (<= x514 n16)))) 
                       (forall ((x516 Int) (x517 A) (x518 A)) 
                           (=> 
                               (and 
                                   (MS1 x516 x517 s37) 
                                   (MS1 x516 x518 s37)) 
                               (= x517 x518))) 
                       (forall ((x519 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x519) 
                                   (<= x519 n16)) 
                               (exists ((x520 A)) 
                                   (MS1 x519 x520 s37))))) 
                   (exists ((n17 Int)) 
                       (and 
                           (<= 0 n17) 
                           (forall ((x521 Int) (x522 A)) 
                               (=> 
                                   (MS1 x521 x522 s37) 
                                   (and 
                                       (<= 1 x521) 
                                       (<= x521 n17)))) 
                           (forall ((x523 Int) (x524 A) (x525 A)) 
                               (=> 
                                   (and 
                                       (MS1 x523 x524 s37) 
                                       (MS1 x523 x525 s37)) 
                                   (= x524 x525))) 
                           (forall ((x526 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x526) 
                                       (<= x526 n17)) 
                                   (exists ((x527 A)) 
                                       (MS1 x526 x527 s37))))))))
         :named hyp64))
(assert (! (forall ((s38 PZA)) 
               (=> 
                   (exists ((n18 Int)) 
                       (and 
                           (<= 0 n18) 
                           (forall ((x528 Int) (x529 A)) 
                               (=> 
                                   (MS1 x528 x529 s38) 
                                   (and 
                                       (<= 1 x528) 
                                       (<= x528 n18)))) 
                           (forall ((x530 Int) (x531 A) (x532 A)) 
                               (=> 
                                   (and 
                                       (MS1 x530 x531 s38) 
                                       (MS1 x530 x532 s38)) 
                                   (= x531 x532))) 
                           (forall ((x533 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x533) 
                                       (<= x533 n18)) 
                                   (exists ((x534 A)) 
                                       (MS1 x533 x534 s38)))))) 
                   (and 
                       (forall ((x535 Int) (x536 A)) 
                           (=> 
                               (MS1 x535 x536 s38) 
                               (and 
                                   (<= 1 x535) 
                                   (forall ((x537 Int)) 
                                       (=> 
                                           (length s38 x537) 
                                           (<= x535 x537)))))) 
                       (forall ((x538 Int) (x539 A) (x540 A)) 
                           (=> 
                               (and 
                                   (MS1 x538 x539 s38) 
                                   (MS1 x538 x540 s38)) 
                               (= x539 x540))) 
                       (forall ((x541 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x541) 
                                   (forall ((x542 Int)) 
                                       (=> 
                                           (length s38 x542) 
                                           (<= x541 x542)))) 
                               (exists ((x543 A)) 
                                   (MS1 x541 x543 s38)))))))
         :named hyp65))
(assert (! (forall ((x544 PZA) (x545 PZA) (x546 PZA)) 
               (= 
                   (cnc x544 x545 x546) 
                   (exists ((s110 PZA) (s210 PZA)) 
                       (and 
                           (exists ((n19 Int)) 
                               (and 
                                   (<= 0 n19) 
                                   (forall ((x547 Int) (x548 A)) 
                                       (=> 
                                           (MS1 x547 x548 s110) 
                                           (and 
                                               (<= 1 x547) 
                                               (<= x547 n19)))) 
                                   (forall ((x549 Int) (x550 A) (x551 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x549 x550 s110) 
                                               (MS1 x549 x551 s110)) 
                                           (= x550 x551))) 
                                   (forall ((x552 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x552) 
                                               (<= x552 n19)) 
                                           (exists ((x553 A)) 
                                               (MS1 x552 x553 s110)))))) 
                           (exists ((n20 Int)) 
                               (and 
                                   (<= 0 n20) 
                                   (forall ((x554 Int) (x555 A)) 
                                       (=> 
                                           (MS1 x554 x555 s210) 
                                           (and 
                                               (<= 1 x554) 
                                               (<= x554 n20)))) 
                                   (forall ((x556 Int) (x557 A) (x558 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x556 x557 s210) 
                                               (MS1 x556 x558 s210)) 
                                           (= x557 x558))) 
                                   (forall ((x559 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x559) 
                                               (<= x559 n20)) 
                                           (exists ((x560 A)) 
                                               (MS1 x559 x560 s210)))))) 
                           (forall ((x561 Int) (x562 A)) 
                               (= 
                                   (MS1 x561 x562 x544) 
                                   (MS1 x561 x562 s110))) 
                           (forall ((x563 Int) (x564 A)) 
                               (= 
                                   (MS1 x563 x564 x545) 
                                   (MS1 x563 x564 s210))) 
                           (forall ((x565 Int) (x566 A)) 
                               (= 
                                   (MS1 x565 x566 x546) 
                                   (or 
                                       (exists ((i17 Int)) 
                                           (and 
                                               (<= 1 i17) 
                                               (forall ((x567 Int)) 
                                                   (=> 
                                                       (length s110 x567) 
                                                       (<= i17 x567))) 
                                               (= x565 i17) 
                                               (MS1 i17 x566 s110))) 
                                       (exists ((i18 Int)) 
                                           (and 
                                               (forall ((x568 Int)) 
                                                   (=> 
                                                       (length s110 x568) 
                                                       (<= (+ x568 1) i18))) 
                                               (forall ((x569 Int) (x570 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s110 x570) 
                                                           (length s210 x569)) 
                                                       (<= i18 (+ x570 x569)))) 
                                               (= x565 i18) 
                                               (exists ((x571 Int)) 
                                                   (and 
                                                       (forall ((x572 Int)) 
                                                           (=> 
                                                               (length s110 x572) 
                                                               (= x571 (- i18 x572)))) 
                                                       (MS1 x571 x566 s210))))))))))))
         :named hyp66))
(assert (! (forall ((s111 PZA) (s211 PZA)) 
               (=> 
                   (and 
                       (exists ((n21 Int)) 
                           (and 
                               (<= 0 n21) 
                               (forall ((x573 Int) (x574 A)) 
                                   (=> 
                                       (MS1 x573 x574 s111) 
                                       (and 
                                           (<= 1 x573) 
                                           (<= x573 n21)))) 
                               (forall ((x575 Int) (x576 A) (x577 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x575 x576 s111) 
                                           (MS1 x575 x577 s111)) 
                                       (= x576 x577))) 
                               (forall ((x578 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x578) 
                                           (<= x578 n21)) 
                                       (exists ((x579 A)) 
                                           (MS1 x578 x579 s111)))))) 
                       (exists ((n22 Int)) 
                           (and 
                               (<= 0 n22) 
                               (forall ((x580 Int) (x581 A)) 
                                   (=> 
                                       (MS1 x580 x581 s211) 
                                       (and 
                                           (<= 1 x580) 
                                           (<= x580 n22)))) 
                               (forall ((x582 Int) (x583 A) (x584 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x582 x583 s211) 
                                           (MS1 x582 x584 s211)) 
                                       (= x583 x584))) 
                               (forall ((x585 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x585) 
                                           (<= x585 n22)) 
                                       (exists ((x586 A)) 
                                           (MS1 x585 x586 s211))))))) 
                   (exists ((x587 PZA) (x588 Int)) 
                       (and 
                           (cnc s111 s211 x587) 
                           (forall ((x589 Int) (x590 Int)) 
                               (=> 
                                   (and 
                                       (length s111 x590) 
                                       (length s211 x589)) 
                                   (= x588 (+ x590 x589)))) 
                           (length x587 x588)))))
         :named hyp67))
(assert (! (forall ((s112 PZA) (s212 PZA)) 
               (=> 
                   (and 
                       (exists ((n23 Int)) 
                           (and 
                               (<= 0 n23) 
                               (forall ((x591 Int) (x592 A)) 
                                   (=> 
                                       (MS1 x591 x592 s112) 
                                       (and 
                                           (<= 1 x591) 
                                           (<= x591 n23)))) 
                               (forall ((x593 Int) (x594 A) (x595 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x593 x594 s112) 
                                           (MS1 x593 x595 s112)) 
                                       (= x594 x595))) 
                               (forall ((x596 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x596) 
                                           (<= x596 n23)) 
                                       (exists ((x597 A)) 
                                           (MS1 x596 x597 s112)))))) 
                       (exists ((n24 Int)) 
                           (and 
                               (<= 0 n24) 
                               (forall ((x598 Int) (x599 A)) 
                                   (=> 
                                       (MS1 x598 x599 s212) 
                                       (and 
                                           (<= 1 x598) 
                                           (<= x598 n24)))) 
                               (forall ((x600 Int) (x601 A) (x602 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x600 x601 s212) 
                                           (MS1 x600 x602 s212)) 
                                       (= x601 x602))) 
                               (forall ((x603 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x603) 
                                           (<= x603 n24)) 
                                       (exists ((x604 A)) 
                                           (MS1 x603 x604 s212))))))) 
                   (forall ((x605 Int)) 
                       (= 
                           (exists ((x606 A) (x607 PZA)) 
                               (and 
                                   (cnc s112 s212 x607) 
                                   (MS1 x605 x606 x607))) 
                           (and 
                               (<= 1 x605) 
                               (forall ((x608 Int) (x609 Int)) 
                                   (=> 
                                       (and 
                                           (length s112 x609) 
                                           (length s212 x608)) 
                                       (<= x605 (+ x609 x608)))))))))
         :named hyp68))
(assert (! (forall ((s113 PZA) (s213 PZA)) 
               (=> 
                   (and 
                       (exists ((n25 Int)) 
                           (and 
                               (<= 0 n25) 
                               (forall ((x610 Int) (x611 A)) 
                                   (=> 
                                       (MS1 x610 x611 s113) 
                                       (and 
                                           (<= 1 x610) 
                                           (<= x610 n25)))) 
                               (forall ((x612 Int) (x613 A) (x614 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x612 x613 s113) 
                                           (MS1 x612 x614 s113)) 
                                       (= x613 x614))) 
                               (forall ((x615 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x615) 
                                           (<= x615 n25)) 
                                       (exists ((x616 A)) 
                                           (MS1 x615 x616 s113)))))) 
                       (exists ((n26 Int)) 
                           (and 
                               (<= 0 n26) 
                               (forall ((x617 Int) (x618 A)) 
                                   (=> 
                                       (MS1 x617 x618 s213) 
                                       (and 
                                           (<= 1 x617) 
                                           (<= x617 n26)))) 
                               (forall ((x619 Int) (x620 A) (x621 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x619 x620 s213) 
                                           (MS1 x619 x621 s213)) 
                                       (= x620 x621))) 
                               (forall ((x622 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x622) 
                                           (<= x622 n26)) 
                                       (exists ((x623 A)) 
                                           (MS1 x622 x623 s213))))))) 
                   (forall ((x624 A)) 
                       (= 
                           (exists ((x625 Int) (x626 PZA)) 
                               (and 
                                   (cnc s113 s213 x626) 
                                   (MS1 x625 x624 x626))) 
                           (or 
                               (exists ((x627 Int)) 
                                   (MS1 x627 x624 s113)) 
                               (exists ((x628 Int)) 
                                   (MS1 x628 x624 s213)))))))
         :named hyp69))
(assert (! (forall ((s114 PZA) (s214 PZA) (i19 Int)) 
               (=> 
                   (and 
                       (exists ((n27 Int)) 
                           (and 
                               (<= 0 n27) 
                               (forall ((x629 Int) (x630 A)) 
                                   (=> 
                                       (MS1 x629 x630 s114) 
                                       (and 
                                           (<= 1 x629) 
                                           (<= x629 n27)))) 
                               (forall ((x631 Int) (x632 A) (x633 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x631 x632 s114) 
                                           (MS1 x631 x633 s114)) 
                                       (= x632 x633))) 
                               (forall ((x634 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x634) 
                                           (<= x634 n27)) 
                                       (exists ((x635 A)) 
                                           (MS1 x634 x635 s114)))))) 
                       (exists ((n28 Int)) 
                           (and 
                               (<= 0 n28) 
                               (forall ((x636 Int) (x637 A)) 
                                   (=> 
                                       (MS1 x636 x637 s214) 
                                       (and 
                                           (<= 1 x636) 
                                           (<= x636 n28)))) 
                               (forall ((x638 Int) (x639 A) (x640 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x638 x639 s214) 
                                           (MS1 x638 x640 s214)) 
                                       (= x639 x640))) 
                               (forall ((x641 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x641) 
                                           (<= x641 n28)) 
                                       (exists ((x642 A)) 
                                           (MS1 x641 x642 s214)))))) 
                       (<= 1 i19) 
                       (forall ((x643 Int)) 
                           (=> 
                               (length s114 x643) 
                               (<= i19 x643)))) 
                   (exists ((x644 PZA)) 
                       (and 
                           (cnc s114 s214 x644) 
                           (exists ((x645 A)) 
                               (and 
                                   (MS1 i19 x645 s114) 
                                   (MS1 i19 x645 x644)))))))
         :named hyp70))
(assert (! (forall ((s115 PZA) (s215 PZA) (i20 Int)) 
               (=> 
                   (and 
                       (exists ((n29 Int)) 
                           (and 
                               (<= 0 n29) 
                               (forall ((x646 Int) (x647 A)) 
                                   (=> 
                                       (MS1 x646 x647 s115) 
                                       (and 
                                           (<= 1 x646) 
                                           (<= x646 n29)))) 
                               (forall ((x648 Int) (x649 A) (x650 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x648 x649 s115) 
                                           (MS1 x648 x650 s115)) 
                                       (= x649 x650))) 
                               (forall ((x651 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x651) 
                                           (<= x651 n29)) 
                                       (exists ((x652 A)) 
                                           (MS1 x651 x652 s115)))))) 
                       (exists ((n30 Int)) 
                           (and 
                               (<= 0 n30) 
                               (forall ((x653 Int) (x654 A)) 
                                   (=> 
                                       (MS1 x653 x654 s215) 
                                       (and 
                                           (<= 1 x653) 
                                           (<= x653 n30)))) 
                               (forall ((x655 Int) (x656 A) (x657 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x655 x656 s215) 
                                           (MS1 x655 x657 s215)) 
                                       (= x656 x657))) 
                               (forall ((x658 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x658) 
                                           (<= x658 n30)) 
                                       (exists ((x659 A)) 
                                           (MS1 x658 x659 s215)))))) 
                       (forall ((x660 Int)) 
                           (=> 
                               (length s115 x660) 
                               (<= (+ x660 1) i20))) 
                       (forall ((x661 Int) (x662 Int)) 
                           (=> 
                               (and 
                                   (length s115 x662) 
                                   (length s215 x661)) 
                               (<= i20 (+ x662 x661))))) 
                   (exists ((x663 PZA)) 
                       (and 
                           (cnc s115 s215 x663) 
                           (exists ((x664 A)) 
                               (and 
                                   (exists ((x665 Int)) 
                                       (and 
                                           (forall ((x666 Int)) 
                                               (=> 
                                                   (length s115 x666) 
                                                   (= x665 (- i20 x666)))) 
                                           (MS1 x665 x664 s215))) 
                                   (MS1 i20 x664 x663)))))))
         :named hyp71))
(assert (! (forall ((x667 PZA) (x668 PZA)) 
               (= 
                   (reverse x667 x668) 
                   (exists ((s39 PZA)) 
                       (and 
                           (exists ((n31 Int)) 
                               (and 
                                   (<= 0 n31) 
                                   (forall ((x669 Int) (x670 A)) 
                                       (=> 
                                           (MS1 x669 x670 s39) 
                                           (and 
                                               (<= 1 x669) 
                                               (<= x669 n31)))) 
                                   (forall ((x671 Int) (x672 A) (x673 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x671 x672 s39) 
                                               (MS1 x671 x673 s39)) 
                                           (= x672 x673))) 
                                   (forall ((x674 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x674) 
                                               (<= x674 n31)) 
                                           (exists ((x675 A)) 
                                               (MS1 x674 x675 s39)))))) 
                           (forall ((x676 Int) (x677 A)) 
                               (= 
                                   (MS1 x676 x677 x667) 
                                   (MS1 x676 x677 s39))) 
                           (forall ((x678 Int) (x679 A)) 
                               (= 
                                   (MS1 x678 x679 x668) 
                                   (exists ((i21 Int)) 
                                       (and 
                                           (<= 1 i21) 
                                           (forall ((x680 Int)) 
                                               (=> 
                                                   (length s39 x680) 
                                                   (<= i21 x680))) 
                                           (= x678 i21) 
                                           (exists ((x681 Int)) 
                                               (and 
                                                   (forall ((x682 Int)) 
                                                       (=> 
                                                           (length s39 x682) 
                                                           (= x681 (+ (- x682 i21) 1)))) 
                                                   (MS1 x681 x679 s39)))))))))))
         :named hyp72))
(assert (! (forall ((s40 PZA)) 
               (=> 
                   (exists ((n32 Int)) 
                       (and 
                           (<= 0 n32) 
                           (forall ((x683 Int) (x684 A)) 
                               (=> 
                                   (MS1 x683 x684 s40) 
                                   (and 
                                       (<= 1 x683) 
                                       (<= x683 n32)))) 
                           (forall ((x685 Int) (x686 A) (x687 A)) 
                               (=> 
                                   (and 
                                       (MS1 x685 x686 s40) 
                                       (MS1 x685 x687 s40)) 
                                   (= x686 x687))) 
                           (forall ((x688 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x688) 
                                       (<= x688 n32)) 
                                   (exists ((x689 A)) 
                                       (MS1 x688 x689 s40)))))) 
                   (exists ((x690 PZA) (x691 Int)) 
                       (and 
                           (reverse s40 x690) 
                           (length s40 x691) 
                           (length x690 x691)))))
         :named hyp73))
(assert (! (forall ((s41 PZA)) 
               (=> 
                   (exists ((n33 Int)) 
                       (and 
                           (<= 0 n33) 
                           (forall ((x692 Int) (x693 A)) 
                               (=> 
                                   (MS1 x692 x693 s41) 
                                   (and 
                                       (<= 1 x692) 
                                       (<= x692 n33)))) 
                           (forall ((x694 Int) (x695 A) (x696 A)) 
                               (=> 
                                   (and 
                                       (MS1 x694 x695 s41) 
                                       (MS1 x694 x696 s41)) 
                                   (= x695 x696))) 
                           (forall ((x697 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x697) 
                                       (<= x697 n33)) 
                                   (exists ((x698 A)) 
                                       (MS1 x697 x698 s41)))))) 
                   (forall ((x699 A)) 
                       (= 
                           (exists ((x700 Int) (x701 PZA)) 
                               (and 
                                   (reverse s41 x701) 
                                   (MS1 x700 x699 x701))) 
                           (exists ((x702 Int)) 
                               (MS1 x702 x699 s41))))))
         :named hyp74))
(assert (! (forall ((s42 PZA)) 
               (=> 
                   (exists ((n34 Int)) 
                       (and 
                           (<= 0 n34) 
                           (forall ((x703 Int) (x704 A)) 
                               (=> 
                                   (MS1 x703 x704 s42) 
                                   (and 
                                       (<= 1 x703) 
                                       (<= x703 n34)))) 
                           (forall ((x705 Int) (x706 A) (x707 A)) 
                               (=> 
                                   (and 
                                       (MS1 x705 x706 s42) 
                                       (MS1 x705 x707 s42)) 
                                   (= x706 x707))) 
                           (forall ((x708 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x708) 
                                       (<= x708 n34)) 
                                   (exists ((x709 A)) 
                                       (MS1 x708 x709 s42)))))) 
                   (exists ((x710 PZA)) 
                       (and 
                           (reverse s42 x710) 
                           (reverse x710 s42)))))
         :named hyp75))
(assert (! (forall ((x711 A) (y19 A) (p14 PZA) (i22 Int)) 
               (=> 
                   (and 
                       (MS0 x711 a) 
                       (MS0 y19 a) 
                       (exists ((n35 Int)) 
                           (and 
                               (<= 0 n35) 
                               (forall ((x712 Int) (x713 A)) 
                                   (=> 
                                       (MS1 x712 x713 p14) 
                                       (and 
                                           (<= 1 x712) 
                                           (<= x712 n35)))) 
                               (forall ((x714 Int) (x715 A) (x716 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x714 x715 p14) 
                                           (MS1 x714 x716 p14)) 
                                       (= x715 x716))) 
                               (forall ((x717 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x717) 
                                           (<= x717 n35)) 
                                       (exists ((x718 A)) 
                                           (MS1 x717 x718 p14)))))) 
                       (shpath x711 y19 p14) 
                       (exists ((x719 A)) 
                           (MS1 i22 x719 p14)) 
                       (not 
                           (= i22 1)) 
                       (not 
                           (length p14 i22))) 
                   (exists ((x720 A) (x721 PZA)) 
                       (and 
                           (MS1 i22 x720 p14) 
                           (forall ((x722 Int) (x723 A)) 
                               (= 
                                   (MS1 x722 x723 x721) 
                                   (and 
                                       (MS1 x722 x723 p14) 
                                       (<= 1 x722) 
                                       (<= x722 i22)))) 
                           (shpath x711 x720 x721)))))
         :named hyp76))
(assert (! (forall ((x724 A) (y22 A) (p15 PZA) (i23 Int)) 
               (=> 
                   (and 
                       (MS0 x724 a) 
                       (MS0 y22 a) 
                       (exists ((n36 Int)) 
                           (and 
                               (<= 0 n36) 
                               (forall ((x725 Int) (x726 A)) 
                                   (=> 
                                       (MS1 x725 x726 p15) 
                                       (and 
                                           (<= 1 x725) 
                                           (<= x725 n36)))) 
                               (forall ((x727 Int) (x728 A) (x729 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x727 x728 p15) 
                                           (MS1 x727 x729 p15)) 
                                       (= x728 x729))) 
                               (forall ((x730 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x730) 
                                           (<= x730 n36)) 
                                       (exists ((x731 A)) 
                                           (MS1 x730 x731 p15)))))) 
                       (shpath x724 y22 p15) 
                       (exists ((x732 A)) 
                           (MS1 i23 x732 p15)) 
                       (not 
                           (= i23 1)) 
                       (not 
                           (length p15 i23))) 
                   (and 
                       (exists ((x733 A)) 
                           (and 
                               (MS1 i23 x733 p15) 
                               (dist x724 x733 i23))) 
                       (exists ((x734 A) (x735 Int)) 
                           (and 
                               (exists ((x736 Int)) 
                                   (and 
                                       (= x736 (+ i23 1)) 
                                       (MS1 x736 x734 p15))) 
                               (= x735 (+ i23 1)) 
                               (dist x724 x734 x735))) 
                       (exists ((x737 A) (x738 A)) 
                           (and 
                               (MS1 i23 x737 p15) 
                               (exists ((x739 Int)) 
                                   (and 
                                       (= x739 (+ i23 1)) 
                                       (MS1 x739 x738 p15))) 
                               (MS x737 x738 r))))))
         :named hyp77))
(assert (! (forall ((x740 A) (y23 A) (p16 PZA) (z2 A)) 
               (=> 
                   (and 
                       (MS0 x740 a) 
                       (MS0 y23 a) 
                       (exists ((n37 Int)) 
                           (and 
                               (<= 0 n37) 
                               (forall ((x741 Int) (x742 A)) 
                                   (=> 
                                       (MS1 x741 x742 p16) 
                                       (and 
                                           (<= 1 x741) 
                                           (<= x741 n37)))) 
                               (forall ((x743 Int) (x744 A) (x745 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x743 x744 p16) 
                                           (MS1 x743 x745 p16)) 
                                       (= x744 x745))) 
                               (forall ((x746 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x746) 
                                           (<= x746 n37)) 
                                       (exists ((x747 A)) 
                                           (MS1 x746 x747 p16)))))) 
                       (shpath x740 y23 p16) 
                       (exists ((x748 Int)) 
                           (MS1 x748 z2 p16)) 
                       (not 
                           (= z2 x740)) 
                       (not 
                           (= z2 y23))) 
                   (exists ((t1 A)) 
                       (and 
                           (MS0 t1 a) 
                           (forall ((x749 Int) (x750 Int)) 
                               (=> 
                                   (and 
                                       (dist x740 z2 x750) 
                                       (dist x740 t1 x749)) 
                                   (< x750 x749))) 
                           (MS z2 t1 r)))))
         :named hyp78))
(assert (! (forall ((s116 PZA) (s216 PZA) (b0 PA)) 
               (=> 
                   (and 
                       (exists ((n38 Int)) 
                           (and 
                               (<= 0 n38) 
                               (forall ((x751 Int) (x752 A)) 
                                   (=> 
                                       (MS1 x751 x752 s116) 
                                       (and 
                                           (<= 1 x751) 
                                           (<= x751 n38)))) 
                               (forall ((x753 Int) (x754 A) (x755 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x753 x754 s116) 
                                           (MS1 x753 x755 s116)) 
                                       (= x754 x755))) 
                               (forall ((x756 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x756) 
                                           (<= x756 n38)) 
                                       (exists ((x757 A)) 
                                           (MS1 x756 x757 s116)))))) 
                       (exists ((n39 Int)) 
                           (and 
                               (<= 0 n39) 
                               (forall ((x758 Int) (x759 A)) 
                                   (=> 
                                       (MS1 x758 x759 s216) 
                                       (and 
                                           (<= 1 x758) 
                                           (<= x758 n39)))) 
                               (forall ((x760 Int) (x761 A) (x762 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x760 x761 s216) 
                                           (MS1 x760 x762 s216)) 
                                       (= x761 x762))) 
                               (forall ((x763 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x763) 
                                           (<= x763 n39)) 
                                       (exists ((x764 A)) 
                                           (MS1 x763 x764 s216)))))) 
                       (forall ((x765 A)) 
                           (=> 
                               (exists ((x766 Int)) 
                                   (MS1 x766 x765 s116)) 
                               (MS0 x765 b0))) 
                       (forall ((x767 A)) 
                           (=> 
                               (exists ((x768 Int)) 
                                   (MS1 x768 x767 s216)) 
                               (MS0 x767 b0)))) 
                   (and 
                       (forall ((x769 Int) (x770 A)) 
                           (=> 
                               (exists ((x771 PZA)) 
                                   (and 
                                       (cnc s116 s216 x771) 
                                       (MS1 x769 x770 x771))) 
                               (and 
                                   (<= 1 x769) 
                                   (forall ((x772 Int) (x773 Int)) 
                                       (=> 
                                           (and 
                                               (length s116 x773) 
                                               (length s216 x772)) 
                                           (<= x769 (+ x773 x772)))) 
                                   (MS0 x770 b0)))) 
                       (forall ((x774 Int) (x775 A) (x776 A)) 
                           (=> 
                               (and 
                                   (exists ((x777 PZA)) 
                                       (and 
                                           (cnc s116 s216 x777) 
                                           (MS1 x774 x775 x777))) 
                                   (exists ((x778 PZA)) 
                                       (and 
                                           (cnc s116 s216 x778) 
                                           (MS1 x774 x776 x778)))) 
                               (= x775 x776))) 
                       (forall ((x779 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x779) 
                                   (forall ((x780 Int) (x781 Int)) 
                                       (=> 
                                           (and 
                                               (length s116 x781) 
                                               (length s216 x780)) 
                                           (<= x779 (+ x781 x780))))) 
                               (exists ((x782 A) (x783 PZA)) 
                                   (and 
                                       (cnc s116 s216 x783) 
                                       (MS1 x779 x782 x783))))))))
         :named hyp79))
(assert (! (forall ((x784 A) (x785 A) (x786 PZA)) 
               (= 
                   (path x784 x785 x786) 
                   (exists ((x787 A) (y24 A) (p17 PZA)) 
                       (and 
                           (exists ((n40 Int)) 
                               (and 
                                   (<= 0 n40) 
                                   (forall ((x788 Int) (x789 A)) 
                                       (=> 
                                           (MS1 x788 x789 p17) 
                                           (and 
                                               (<= 1 x788) 
                                               (<= x788 n40)))) 
                                   (forall ((x790 Int) (x791 A) (x792 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x790 x791 p17) 
                                               (MS1 x790 x792 p17)) 
                                           (= x791 x792))) 
                                   (forall ((x793 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x793) 
                                               (<= x793 n40)) 
                                           (exists ((x794 A)) 
                                               (MS1 x793 x794 p17)))))) 
                           (forall ((x795 A)) 
                               (=> 
                                   (exists ((x796 Int)) 
                                       (MS1 x796 x795 p17)) 
                                   (MS0 x795 a))) 
                           (forall ((x797 Int)) 
                               (=> 
                                   (length p17 x797) 
                                   (< 1 x797))) 
                           (exists ((x798 Int)) 
                               (and 
                                   (= x798 1) 
                                   (MS1 x798 x787 p17))) 
                           (exists ((x799 Int)) 
                               (and 
                                   (length p17 x799) 
                                   (MS1 x799 y24 p17))) 
                           (forall ((i24 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i24) 
                                       (forall ((x800 Int)) 
                                           (=> 
                                               (length p17 x800) 
                                               (<= i24 (- x800 1))))) 
                                   (exists ((x801 A) (x802 A)) 
                                       (and 
                                           (MS1 i24 x801 p17) 
                                           (exists ((x803 Int)) 
                                               (and 
                                                   (= x803 (+ i24 1)) 
                                                   (MS1 x803 x802 p17))) 
                                           (MS x801 x802 r))))) 
                           (= x784 x787) 
                           (= x785 y24) 
                           (forall ((x804 Int) (x805 A)) 
                               (= 
                                   (MS1 x804 x805 x786) 
                                   (MS1 x804 x805 p17)))))))
         :named hyp80))
(assert (! (forall ((x806 A) (y25 A)) 
               (=> 
                   (and 
                       (MS0 x806 a) 
                       (MS0 y25 a)) 
                   (exists ((p18 PZA)) 
                       (and 
                           (path x806 y25 p18) 
                           (exists ((x807 Int)) 
                               (and 
                                   (length p18 x807) 
                                   (dist x806 y25 x807)))))))
         :named hyp81))
(assert (! (path x y p)
         :named hyp82))
(assert (! (exists ((x808 Int)) 
               (and 
                   (length p x808) 
                   (dist x y x808)))
         :named hyp83))
(assert (! (forall ((x809 A) (y26 A) (p19 PZA) (i25 Int)) 
               (=> 
                   (and 
                       (MS0 x809 a) 
                       (MS0 y26 a) 
                       (exists ((n41 Int)) 
                           (and 
                               (<= 0 n41) 
                               (forall ((x810 Int) (x811 A)) 
                                   (=> 
                                       (MS1 x810 x811 p19) 
                                       (and 
                                           (<= 1 x810) 
                                           (<= x810 n41)))) 
                               (forall ((x812 Int) (x813 A) (x814 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x812 x813 p19) 
                                           (MS1 x812 x814 p19)) 
                                       (= x813 x814))) 
                               (forall ((x815 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x815) 
                                           (<= x815 n41)) 
                                       (exists ((x816 A)) 
                                           (MS1 x815 x816 p19)))))) 
                       (path x809 y26 p19) 
                       (exists ((x817 Int)) 
                           (and 
                               (length p19 x817) 
                               (dist x809 y26 x817))) 
                       (exists ((x818 A)) 
                           (MS1 i25 x818 p19)) 
                       (not 
                           (= i25 1)) 
                       (not 
                           (length p19 i25))) 
                   (and 
                       (exists ((x819 A) (x820 PZA)) 
                           (and 
                               (MS1 i25 x819 p19) 
                               (forall ((x821 Int) (x822 A)) 
                                   (= 
                                       (MS1 x821 x822 x820) 
                                       (and 
                                           (MS1 x821 x822 p19) 
                                           (<= 1 x821) 
                                           (<= x821 i25)))) 
                               (path x809 x819 x820))) 
                       (exists ((x823 A) (x824 Int)) 
                           (and 
                               (MS1 i25 x823 p19) 
                               (exists ((x825 PZA)) 
                                   (and 
                                       (forall ((x826 Int) (x827 A)) 
                                           (= 
                                               (MS1 x826 x827 x825) 
                                               (and 
                                                   (MS1 x826 x827 p19) 
                                                   (<= 1 x826) 
                                                   (<= x826 i25)))) 
                                       (length x825 x824))) 
                               (dist x809 x823 x824))))))
         :named hyp84))
(assert (! (forall ((x828 A) (y27 A) (p20 PZA) (i26 Int)) 
               (=> 
                   (and 
                       (MS0 x828 a) 
                       (MS0 y27 a) 
                       (exists ((n42 Int)) 
                           (and 
                               (<= 0 n42) 
                               (forall ((x829 Int) (x830 A)) 
                                   (=> 
                                       (MS1 x829 x830 p20) 
                                       (and 
                                           (<= 1 x829) 
                                           (<= x829 n42)))) 
                               (forall ((x831 Int) (x832 A) (x833 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x831 x832 p20) 
                                           (MS1 x831 x833 p20)) 
                                       (= x832 x833))) 
                               (forall ((x834 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x834) 
                                           (<= x834 n42)) 
                                       (exists ((x835 A)) 
                                           (MS1 x834 x835 p20)))))) 
                       (path x828 y27 p20) 
                       (exists ((x836 Int)) 
                           (and 
                               (length p20 x836) 
                               (dist x828 y27 x836))) 
                       (exists ((x837 A)) 
                           (MS1 i26 x837 p20)) 
                       (not 
                           (= i26 1)) 
                       (not 
                           (length p20 i26))) 
                   (and 
                       (exists ((x838 A)) 
                           (and 
                               (MS1 i26 x838 p20) 
                               (dist x828 x838 i26))) 
                       (exists ((x839 A) (x840 Int)) 
                           (and 
                               (exists ((x841 Int)) 
                                   (and 
                                       (= x841 (+ i26 1)) 
                                       (MS1 x841 x839 p20))) 
                               (= x840 (+ i26 1)) 
                               (dist x828 x839 x840))) 
                       (exists ((x842 A) (x843 A)) 
                           (and 
                               (MS1 i26 x842 p20) 
                               (exists ((x844 Int)) 
                                   (and 
                                       (= x844 (+ i26 1)) 
                                       (MS1 x844 x843 p20))) 
                               (MS x842 x843 r))))))
         :named hyp85))
(assert (! (forall ((x845 A) (y28 A) (p21 PZA) (z3 A)) 
               (=> 
                   (and 
                       (MS0 x845 a) 
                       (MS0 y28 a) 
                       (exists ((n43 Int)) 
                           (and 
                               (<= 0 n43) 
                               (forall ((x846 Int) (x847 A)) 
                                   (=> 
                                       (MS1 x846 x847 p21) 
                                       (and 
                                           (<= 1 x846) 
                                           (<= x846 n43)))) 
                               (forall ((x848 Int) (x849 A) (x850 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x848 x849 p21) 
                                           (MS1 x848 x850 p21)) 
                                       (= x849 x850))) 
                               (forall ((x851 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x851) 
                                           (<= x851 n43)) 
                                       (exists ((x852 A)) 
                                           (MS1 x851 x852 p21)))))) 
                       (path x845 y28 p21) 
                       (exists ((x853 Int)) 
                           (and 
                               (length p21 x853) 
                               (dist x845 y28 x853))) 
                       (exists ((x854 Int)) 
                           (MS1 x854 z3 p21)) 
                       (not 
                           (= z3 x845)) 
                       (not 
                           (= z3 y28))) 
                   (exists ((t2 A)) 
                       (and 
                           (MS0 t2 a) 
                           (forall ((x855 Int) (x856 Int)) 
                               (=> 
                                   (and 
                                       (dist x845 z3 x856) 
                                       (dist x845 t2 x855)) 
                                   (< x856 x855))) 
                           (MS z3 t2 r)))))
         :named hyp86))
(assert (! (and 
               (forall ((x857 PZA) (x858 PZA) (x859 PZA)) 
                   (=> 
                       (exists ((s117 PZA) (s217 PZA)) 
                           (and 
                               (exists ((n44 Int)) 
                                   (and 
                                       (<= 0 n44) 
                                       (forall ((x860 Int) (x861 A)) 
                                           (=> 
                                               (MS1 x860 x861 s117) 
                                               (and 
                                                   (<= 1 x860) 
                                                   (<= x860 n44)))) 
                                       (forall ((x862 Int) (x863 A) (x864 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x862 x863 s117) 
                                                   (MS1 x862 x864 s117)) 
                                               (= x863 x864))) 
                                       (forall ((x865 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x865) 
                                                   (<= x865 n44)) 
                                               (exists ((x866 A)) 
                                                   (MS1 x865 x866 s117)))))) 
                               (exists ((n45 Int)) 
                                   (and 
                                       (<= 0 n45) 
                                       (forall ((x867 Int) (x868 A)) 
                                           (=> 
                                               (MS1 x867 x868 s217) 
                                               (and 
                                                   (<= 1 x867) 
                                                   (<= x867 n45)))) 
                                       (forall ((x869 Int) (x870 A) (x871 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x869 x870 s217) 
                                                   (MS1 x869 x871 s217)) 
                                               (= x870 x871))) 
                                       (forall ((x872 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x872) 
                                                   (<= x872 n45)) 
                                               (exists ((x873 A)) 
                                                   (MS1 x872 x873 s217)))))) 
                               (forall ((x874 Int) (x875 A)) 
                                   (= 
                                       (MS1 x874 x875 x857) 
                                       (MS1 x874 x875 s117))) 
                               (forall ((x876 Int) (x877 A)) 
                                   (= 
                                       (MS1 x876 x877 x858) 
                                       (MS1 x876 x877 s217))) 
                               (forall ((x878 Int) (x879 A)) 
                                   (= 
                                       (MS1 x878 x879 x859) 
                                       (or 
                                           (exists ((i27 Int)) 
                                               (and 
                                                   (<= 1 i27) 
                                                   (forall ((x880 Int)) 
                                                       (=> 
                                                           (length s117 x880) 
                                                           (<= i27 x880))) 
                                                   (= x878 i27) 
                                                   (MS1 i27 x879 s117))) 
                                           (exists ((i28 Int)) 
                                               (and 
                                                   (forall ((x881 Int)) 
                                                       (=> 
                                                           (length s117 x881) 
                                                           (<= (+ x881 1) i28))) 
                                                   (forall ((x882 Int) (x883 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s117 x883) 
                                                               (length s217 x882)) 
                                                           (<= i28 (+ x883 x882)))) 
                                                   (= x878 i28) 
                                                   (exists ((x884 Int)) 
                                                       (and 
                                                           (forall ((x885 Int)) 
                                                               (=> 
                                                                   (length s117 x885) 
                                                                   (= x884 (- i28 x885)))) 
                                                           (MS1 x884 x879 s217)))))))))) 
                       (and 
                           (exists ((s43 PZA)) 
                               (and 
                                   (exists ((n46 Int)) 
                                       (and 
                                           (<= 0 n46) 
                                           (forall ((x886 Int) (x887 A)) 
                                               (=> 
                                                   (MS1 x886 x887 s43) 
                                                   (and 
                                                       (<= 1 x886) 
                                                       (<= x886 n46)))) 
                                           (forall ((x888 Int) (x889 A) (x890 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x888 x889 s43) 
                                                       (MS1 x888 x890 s43)) 
                                                   (= x889 x890))) 
                                           (forall ((x891 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x891) 
                                                       (<= x891 n46)) 
                                                   (exists ((x892 A)) 
                                                       (MS1 x891 x892 s43)))))) 
                                   (forall ((x893 Int) (x894 A)) 
                                       (= 
                                           (MS1 x893 x894 x857) 
                                           (MS1 x893 x894 s43))))) 
                           (exists ((s44 PZA)) 
                               (and 
                                   (exists ((n47 Int)) 
                                       (and 
                                           (<= 0 n47) 
                                           (forall ((x895 Int) (x896 A)) 
                                               (=> 
                                                   (MS1 x895 x896 s44) 
                                                   (and 
                                                       (<= 1 x895) 
                                                       (<= x895 n47)))) 
                                           (forall ((x897 Int) (x898 A) (x899 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x897 x898 s44) 
                                                       (MS1 x897 x899 s44)) 
                                                   (= x898 x899))) 
                                           (forall ((x900 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x900) 
                                                       (<= x900 n47)) 
                                                   (exists ((x901 A)) 
                                                       (MS1 x900 x901 s44)))))) 
                                   (forall ((x902 Int) (x903 A)) 
                                       (= 
                                           (MS1 x902 x903 x858) 
                                           (MS1 x902 x903 s44))))) 
                           (exists ((s45 PZA)) 
                               (and 
                                   (exists ((n48 Int)) 
                                       (and 
                                           (<= 0 n48) 
                                           (forall ((x904 Int) (x905 A)) 
                                               (=> 
                                                   (MS1 x904 x905 s45) 
                                                   (and 
                                                       (<= 1 x904) 
                                                       (<= x904 n48)))) 
                                           (forall ((x906 Int) (x907 A) (x908 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x906 x907 s45) 
                                                       (MS1 x906 x908 s45)) 
                                                   (= x907 x908))) 
                                           (forall ((x909 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x909) 
                                                       (<= x909 n48)) 
                                                   (exists ((x910 A)) 
                                                       (MS1 x909 x910 s45)))))) 
                                   (forall ((x911 Int) (x912 A)) 
                                       (= 
                                           (MS1 x911 x912 x859) 
                                           (MS1 x911 x912 s45)))))))) 
               (forall ((x913 PZA) (x914 PZA) (x915 PZA) (x916 PZA)) 
                   (=> 
                       (and 
                           (exists ((s118 PZA) (s218 PZA)) 
                               (and 
                                   (exists ((n49 Int)) 
                                       (and 
                                           (<= 0 n49) 
                                           (forall ((x917 Int) (x918 A)) 
                                               (=> 
                                                   (MS1 x917 x918 s118) 
                                                   (and 
                                                       (<= 1 x917) 
                                                       (<= x917 n49)))) 
                                           (forall ((x919 Int) (x920 A) (x921 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x919 x920 s118) 
                                                       (MS1 x919 x921 s118)) 
                                                   (= x920 x921))) 
                                           (forall ((x922 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x922) 
                                                       (<= x922 n49)) 
                                                   (exists ((x923 A)) 
                                                       (MS1 x922 x923 s118)))))) 
                                   (exists ((n50 Int)) 
                                       (and 
                                           (<= 0 n50) 
                                           (forall ((x924 Int) (x925 A)) 
                                               (=> 
                                                   (MS1 x924 x925 s218) 
                                                   (and 
                                                       (<= 1 x924) 
                                                       (<= x924 n50)))) 
                                           (forall ((x926 Int) (x927 A) (x928 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x926 x927 s218) 
                                                       (MS1 x926 x928 s218)) 
                                                   (= x927 x928))) 
                                           (forall ((x929 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x929) 
                                                       (<= x929 n50)) 
                                                   (exists ((x930 A)) 
                                                       (MS1 x929 x930 s218)))))) 
                                   (forall ((x931 Int) (x932 A)) 
                                       (= 
                                           (MS1 x931 x932 x913) 
                                           (MS1 x931 x932 s118))) 
                                   (forall ((x933 Int) (x934 A)) 
                                       (= 
                                           (MS1 x933 x934 x914) 
                                           (MS1 x933 x934 s218))) 
                                   (forall ((x935 Int) (x936 A)) 
                                       (= 
                                           (MS1 x935 x936 x915) 
                                           (or 
                                               (exists ((i29 Int)) 
                                                   (and 
                                                       (<= 1 i29) 
                                                       (forall ((x937 Int)) 
                                                           (=> 
                                                               (length s118 x937) 
                                                               (<= i29 x937))) 
                                                       (= x935 i29) 
                                                       (MS1 i29 x936 s118))) 
                                               (exists ((i30 Int)) 
                                                   (and 
                                                       (forall ((x938 Int)) 
                                                           (=> 
                                                               (length s118 x938) 
                                                               (<= (+ x938 1) i30))) 
                                                       (forall ((x939 Int) (x940 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s118 x940) 
                                                                   (length s218 x939)) 
                                                               (<= i30 (+ x940 x939)))) 
                                                       (= x935 i30) 
                                                       (exists ((x941 Int)) 
                                                           (and 
                                                               (forall ((x942 Int)) 
                                                                   (=> 
                                                                       (length s118 x942) 
                                                                       (= x941 (- i30 x942)))) 
                                                               (MS1 x941 x936 s218)))))))))) 
                           (exists ((s119 PZA) (s219 PZA)) 
                               (and 
                                   (exists ((n51 Int)) 
                                       (and 
                                           (<= 0 n51) 
                                           (forall ((x943 Int) (x944 A)) 
                                               (=> 
                                                   (MS1 x943 x944 s119) 
                                                   (and 
                                                       (<= 1 x943) 
                                                       (<= x943 n51)))) 
                                           (forall ((x945 Int) (x946 A) (x947 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x945 x946 s119) 
                                                       (MS1 x945 x947 s119)) 
                                                   (= x946 x947))) 
                                           (forall ((x948 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x948) 
                                                       (<= x948 n51)) 
                                                   (exists ((x949 A)) 
                                                       (MS1 x948 x949 s119)))))) 
                                   (exists ((n52 Int)) 
                                       (and 
                                           (<= 0 n52) 
                                           (forall ((x950 Int) (x951 A)) 
                                               (=> 
                                                   (MS1 x950 x951 s219) 
                                                   (and 
                                                       (<= 1 x950) 
                                                       (<= x950 n52)))) 
                                           (forall ((x952 Int) (x953 A) (x954 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x952 x953 s219) 
                                                       (MS1 x952 x954 s219)) 
                                                   (= x953 x954))) 
                                           (forall ((x955 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x955) 
                                                       (<= x955 n52)) 
                                                   (exists ((x956 A)) 
                                                       (MS1 x955 x956 s219)))))) 
                                   (forall ((x957 Int) (x958 A)) 
                                       (= 
                                           (MS1 x957 x958 x913) 
                                           (MS1 x957 x958 s119))) 
                                   (forall ((x959 Int) (x960 A)) 
                                       (= 
                                           (MS1 x959 x960 x914) 
                                           (MS1 x959 x960 s219))) 
                                   (forall ((x961 Int) (x962 A)) 
                                       (= 
                                           (MS1 x961 x962 x916) 
                                           (or 
                                               (exists ((i31 Int)) 
                                                   (and 
                                                       (<= 1 i31) 
                                                       (forall ((x963 Int)) 
                                                           (=> 
                                                               (length s119 x963) 
                                                               (<= i31 x963))) 
                                                       (= x961 i31) 
                                                       (MS1 i31 x962 s119))) 
                                               (exists ((i32 Int)) 
                                                   (and 
                                                       (forall ((x964 Int)) 
                                                           (=> 
                                                               (length s119 x964) 
                                                               (<= (+ x964 1) i32))) 
                                                       (forall ((x965 Int) (x966 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length s119 x966) 
                                                                   (length s219 x965)) 
                                                               (<= i32 (+ x966 x965)))) 
                                                       (= x961 i32) 
                                                       (exists ((x967 Int)) 
                                                           (and 
                                                               (forall ((x968 Int)) 
                                                                   (=> 
                                                                       (length s119 x968) 
                                                                       (= x967 (- i32 x968)))) 
                                                               (MS1 x967 x962 s219))))))))))) 
                       (forall ((x969 Int) (x970 A)) 
                           (= 
                               (MS1 x969 x970 x915) 
                               (MS1 x969 x970 x916))))) 
               (forall ((x971 PZA) (x972 PZA)) 
                   (=> 
                       (and 
                           (exists ((s46 PZA)) 
                               (and 
                                   (exists ((n53 Int)) 
                                       (and 
                                           (<= 0 n53) 
                                           (forall ((x973 Int) (x974 A)) 
                                               (=> 
                                                   (MS1 x973 x974 s46) 
                                                   (and 
                                                       (<= 1 x973) 
                                                       (<= x973 n53)))) 
                                           (forall ((x975 Int) (x976 A) (x977 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x975 x976 s46) 
                                                       (MS1 x975 x977 s46)) 
                                                   (= x976 x977))) 
                                           (forall ((x978 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x978) 
                                                       (<= x978 n53)) 
                                                   (exists ((x979 A)) 
                                                       (MS1 x978 x979 s46)))))) 
                                   (forall ((x980 Int) (x981 A)) 
                                       (= 
                                           (MS1 x980 x981 x971) 
                                           (MS1 x980 x981 s46))))) 
                           (exists ((s47 PZA)) 
                               (and 
                                   (exists ((n54 Int)) 
                                       (and 
                                           (<= 0 n54) 
                                           (forall ((x982 Int) (x983 A)) 
                                               (=> 
                                                   (MS1 x982 x983 s47) 
                                                   (and 
                                                       (<= 1 x982) 
                                                       (<= x982 n54)))) 
                                           (forall ((x984 Int) (x985 A) (x986 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x984 x985 s47) 
                                                       (MS1 x984 x986 s47)) 
                                                   (= x985 x986))) 
                                           (forall ((x987 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x987) 
                                                       (<= x987 n54)) 
                                                   (exists ((x988 A)) 
                                                       (MS1 x987 x988 s47)))))) 
                                   (forall ((x989 Int) (x990 A)) 
                                       (= 
                                           (MS1 x989 x990 x972) 
                                           (MS1 x989 x990 s47)))))) 
                       (exists ((x991 PZA) (s120 PZA) (s220 PZA)) 
                           (and 
                               (exists ((n55 Int)) 
                                   (and 
                                       (<= 0 n55) 
                                       (forall ((x992 Int) (x993 A)) 
                                           (=> 
                                               (MS1 x992 x993 s120) 
                                               (and 
                                                   (<= 1 x992) 
                                                   (<= x992 n55)))) 
                                       (forall ((x994 Int) (x995 A) (x996 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x994 x995 s120) 
                                                   (MS1 x994 x996 s120)) 
                                               (= x995 x996))) 
                                       (forall ((x997 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x997) 
                                                   (<= x997 n55)) 
                                               (exists ((x998 A)) 
                                                   (MS1 x997 x998 s120)))))) 
                               (exists ((n56 Int)) 
                                   (and 
                                       (<= 0 n56) 
                                       (forall ((x999 Int) (x1000 A)) 
                                           (=> 
                                               (MS1 x999 x1000 s220) 
                                               (and 
                                                   (<= 1 x999) 
                                                   (<= x999 n56)))) 
                                       (forall ((x1001 Int) (x1002 A) (x1003 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x1001 x1002 s220) 
                                                   (MS1 x1001 x1003 s220)) 
                                               (= x1002 x1003))) 
                                       (forall ((x1004 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1004) 
                                                   (<= x1004 n56)) 
                                               (exists ((x1005 A)) 
                                                   (MS1 x1004 x1005 s220)))))) 
                               (forall ((x1006 Int) (x1007 A)) 
                                   (= 
                                       (MS1 x1006 x1007 x971) 
                                       (MS1 x1006 x1007 s120))) 
                               (forall ((x1008 Int) (x1009 A)) 
                                   (= 
                                       (MS1 x1008 x1009 x972) 
                                       (MS1 x1008 x1009 s220))) 
                               (forall ((x1010 Int) (x1011 A)) 
                                   (= 
                                       (MS1 x1010 x1011 x991) 
                                       (or 
                                           (exists ((i33 Int)) 
                                               (and 
                                                   (<= 1 i33) 
                                                   (forall ((x1012 Int)) 
                                                       (=> 
                                                           (length s120 x1012) 
                                                           (<= i33 x1012))) 
                                                   (= x1010 i33) 
                                                   (MS1 i33 x1011 s120))) 
                                           (exists ((i34 Int)) 
                                               (and 
                                                   (forall ((x1013 Int)) 
                                                       (=> 
                                                           (length s120 x1013) 
                                                           (<= (+ x1013 1) i34))) 
                                                   (forall ((x1014 Int) (x1015 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length s120 x1015) 
                                                               (length s220 x1014)) 
                                                           (<= i34 (+ x1015 x1014)))) 
                                                   (= x1010 i34) 
                                                   (exists ((x1016 Int)) 
                                                       (and 
                                                           (forall ((x1017 Int)) 
                                                               (=> 
                                                                   (length s120 x1017) 
                                                                   (= x1016 (- i34 x1017)))) 
                                                           (MS1 x1016 x1011 s220)))))))))))))
         :named hyp87))
(assert (! (forall ((y110 A) (y29 A) (x1018 A) (x1101 A) (p22 PZA) (q1 PZA)) 
               (=> 
                   (and 
                       (MS0 y110 a) 
                       (MS0 y29 a) 
                       (MS0 x1018 a) 
                       (MS0 x1101 a) 
                       (path x1018 y110 q1) 
                       (path y29 x1101 p22) 
                       (MS x1101 x1018 r)) 
                   (exists ((x1019 PZA)) 
                       (and 
                           (forall ((x1020 Int) (x1021 A)) 
                               (= 
                                   (MS1 x1020 x1021 x1019) 
                                   (or 
                                       (exists ((i35 Int)) 
                                           (and 
                                               (<= 1 i35) 
                                               (forall ((x1022 Int)) 
                                                   (=> 
                                                       (length p22 x1022) 
                                                       (<= i35 x1022))) 
                                               (= x1020 i35) 
                                               (MS1 i35 x1021 p22))) 
                                       (exists ((i36 Int)) 
                                           (and 
                                               (forall ((x1023 Int)) 
                                                   (=> 
                                                       (length p22 x1023) 
                                                       (<= (+ x1023 1) i36))) 
                                               (forall ((x1024 Int) (x1025 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length p22 x1025) 
                                                           (length q1 x1024)) 
                                                       (<= i36 (+ x1025 x1024)))) 
                                               (= x1020 i36) 
                                               (exists ((x1026 Int)) 
                                                   (and 
                                                       (forall ((x1027 Int)) 
                                                           (=> 
                                                               (length p22 x1027) 
                                                               (= x1026 (- i36 x1027)))) 
                                                       (MS1 x1026 x1021 q1)))))))) 
                           (path y29 y110 x1019)))))
         :named hyp88))
(assert (! (forall ((s121 PZA) (s221 PZA)) 
               (=> 
                   (and 
                       (exists ((n57 Int)) 
                           (and 
                               (<= 0 n57) 
                               (forall ((x1028 Int) (x1029 A)) 
                                   (=> 
                                       (MS1 x1028 x1029 s121) 
                                       (and 
                                           (<= 1 x1028) 
                                           (<= x1028 n57)))) 
                               (forall ((x1030 Int) (x1031 A) (x1032 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1030 x1031 s121) 
                                           (MS1 x1030 x1032 s121)) 
                                       (= x1031 x1032))) 
                               (forall ((x1033 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1033) 
                                           (<= x1033 n57)) 
                                       (exists ((x1034 A)) 
                                           (MS1 x1033 x1034 s121)))))) 
                       (exists ((n58 Int)) 
                           (and 
                               (<= 0 n58) 
                               (forall ((x1035 Int) (x1036 A)) 
                                   (=> 
                                       (MS1 x1035 x1036 s221) 
                                       (and 
                                           (<= 1 x1035) 
                                           (<= x1035 n58)))) 
                               (forall ((x1037 Int) (x1038 A) (x1039 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1037 x1038 s221) 
                                           (MS1 x1037 x1039 s221)) 
                                       (= x1038 x1039))) 
                               (forall ((x1040 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1040) 
                                           (<= x1040 n58)) 
                                       (exists ((x1041 A)) 
                                           (MS1 x1040 x1041 s221))))))) 
                   (exists ((x1042 PZA) (x1043 Int)) 
                       (and 
                           (forall ((x1044 Int) (x1045 A)) 
                               (= 
                                   (MS1 x1044 x1045 x1042) 
                                   (or 
                                       (exists ((i37 Int)) 
                                           (and 
                                               (<= 1 i37) 
                                               (forall ((x1046 Int)) 
                                                   (=> 
                                                       (length s121 x1046) 
                                                       (<= i37 x1046))) 
                                               (= x1044 i37) 
                                               (MS1 i37 x1045 s121))) 
                                       (exists ((i38 Int)) 
                                           (and 
                                               (forall ((x1047 Int)) 
                                                   (=> 
                                                       (length s121 x1047) 
                                                       (<= (+ x1047 1) i38))) 
                                               (forall ((x1048 Int) (x1049 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s121 x1049) 
                                                           (length s221 x1048)) 
                                                       (<= i38 (+ x1049 x1048)))) 
                                               (= x1044 i38) 
                                               (exists ((x1050 Int)) 
                                                   (and 
                                                       (forall ((x1051 Int)) 
                                                           (=> 
                                                               (length s121 x1051) 
                                                               (= x1050 (- i38 x1051)))) 
                                                       (MS1 x1050 x1045 s221)))))))) 
                           (forall ((x1052 Int) (x1053 Int)) 
                               (=> 
                                   (and 
                                       (length s121 x1053) 
                                       (length s221 x1052)) 
                                   (= x1043 (+ x1053 x1052)))) 
                           (length x1042 x1043)))))
         :named hyp89))
(assert (! (forall ((s122 PZA) (s222 PZA)) 
               (=> 
                   (and 
                       (exists ((n59 Int)) 
                           (and 
                               (<= 0 n59) 
                               (forall ((x1054 Int) (x1055 A)) 
                                   (=> 
                                       (MS1 x1054 x1055 s122) 
                                       (and 
                                           (<= 1 x1054) 
                                           (<= x1054 n59)))) 
                               (forall ((x1056 Int) (x1057 A) (x1058 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1056 x1057 s122) 
                                           (MS1 x1056 x1058 s122)) 
                                       (= x1057 x1058))) 
                               (forall ((x1059 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1059) 
                                           (<= x1059 n59)) 
                                       (exists ((x1060 A)) 
                                           (MS1 x1059 x1060 s122)))))) 
                       (exists ((n60 Int)) 
                           (and 
                               (<= 0 n60) 
                               (forall ((x1061 Int) (x1062 A)) 
                                   (=> 
                                       (MS1 x1061 x1062 s222) 
                                       (and 
                                           (<= 1 x1061) 
                                           (<= x1061 n60)))) 
                               (forall ((x1063 Int) (x1064 A) (x1065 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1063 x1064 s222) 
                                           (MS1 x1063 x1065 s222)) 
                                       (= x1064 x1065))) 
                               (forall ((x1066 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1066) 
                                           (<= x1066 n60)) 
                                       (exists ((x1067 A)) 
                                           (MS1 x1066 x1067 s222))))))) 
                   (forall ((x1068 Int)) 
                       (= 
                           (or 
                               (exists ((x1069 A)) 
                                   (exists ((i39 Int)) 
                                       (and 
                                           (<= 1 i39) 
                                           (forall ((x1070 Int)) 
                                               (=> 
                                                   (length s122 x1070) 
                                                   (<= i39 x1070))) 
                                           (= x1068 i39) 
                                           (MS1 i39 x1069 s122)))) 
                               (exists ((x1071 A)) 
                                   (exists ((i40 Int)) 
                                       (and 
                                           (forall ((x1072 Int)) 
                                               (=> 
                                                   (length s122 x1072) 
                                                   (<= (+ x1072 1) i40))) 
                                           (forall ((x1073 Int) (x1074 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s122 x1074) 
                                                       (length s222 x1073)) 
                                                   (<= i40 (+ x1074 x1073)))) 
                                           (= x1068 i40) 
                                           (exists ((x1075 Int)) 
                                               (and 
                                                   (forall ((x1076 Int)) 
                                                       (=> 
                                                           (length s122 x1076) 
                                                           (= x1075 (- i40 x1076)))) 
                                                   (MS1 x1075 x1071 s222))))))) 
                           (and 
                               (<= 1 x1068) 
                               (forall ((x1077 Int) (x1078 Int)) 
                                   (=> 
                                       (and 
                                           (length s122 x1078) 
                                           (length s222 x1077)) 
                                       (<= x1068 (+ x1078 x1077)))))))))
         :named hyp90))
(assert (! (forall ((s123 PZA) (s223 PZA)) 
               (=> 
                   (and 
                       (exists ((n61 Int)) 
                           (and 
                               (<= 0 n61) 
                               (forall ((x1079 Int) (x1080 A)) 
                                   (=> 
                                       (MS1 x1079 x1080 s123) 
                                       (and 
                                           (<= 1 x1079) 
                                           (<= x1079 n61)))) 
                               (forall ((x1081 Int) (x1082 A) (x1083 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1081 x1082 s123) 
                                           (MS1 x1081 x1083 s123)) 
                                       (= x1082 x1083))) 
                               (forall ((x1084 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1084) 
                                           (<= x1084 n61)) 
                                       (exists ((x1085 A)) 
                                           (MS1 x1084 x1085 s123)))))) 
                       (exists ((n62 Int)) 
                           (and 
                               (<= 0 n62) 
                               (forall ((x1086 Int) (x1087 A)) 
                                   (=> 
                                       (MS1 x1086 x1087 s223) 
                                       (and 
                                           (<= 1 x1086) 
                                           (<= x1086 n62)))) 
                               (forall ((x1088 Int) (x1089 A) (x1090 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1088 x1089 s223) 
                                           (MS1 x1088 x1090 s223)) 
                                       (= x1089 x1090))) 
                               (forall ((x1091 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1091) 
                                           (<= x1091 n62)) 
                                       (exists ((x1092 A)) 
                                           (MS1 x1091 x1092 s223))))))) 
                   (forall ((x1093 A)) 
                       (= 
                           (or 
                               (exists ((x1094 Int)) 
                                   (exists ((i41 Int)) 
                                       (and 
                                           (<= 1 i41) 
                                           (forall ((x1095 Int)) 
                                               (=> 
                                                   (length s123 x1095) 
                                                   (<= i41 x1095))) 
                                           (= x1094 i41) 
                                           (MS1 i41 x1093 s123)))) 
                               (exists ((x1096 Int)) 
                                   (exists ((i42 Int)) 
                                       (and 
                                           (forall ((x1097 Int)) 
                                               (=> 
                                                   (length s123 x1097) 
                                                   (<= (+ x1097 1) i42))) 
                                           (forall ((x1098 Int) (x1099 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s123 x1099) 
                                                       (length s223 x1098)) 
                                                   (<= i42 (+ x1099 x1098)))) 
                                           (= x1096 i42) 
                                           (exists ((x1102 Int)) 
                                               (and 
                                                   (forall ((x1103 Int)) 
                                                       (=> 
                                                           (length s123 x1103) 
                                                           (= x1102 (- i42 x1103)))) 
                                                   (MS1 x1102 x1093 s223))))))) 
                           (or 
                               (exists ((x1104 Int)) 
                                   (MS1 x1104 x1093 s123)) 
                               (exists ((x1105 Int)) 
                                   (MS1 x1105 x1093 s223)))))))
         :named hyp91))
(assert (! (forall ((s124 PZA) (s224 PZA) (i43 Int)) 
               (=> 
                   (and 
                       (exists ((n63 Int)) 
                           (and 
                               (<= 0 n63) 
                               (forall ((x1106 Int) (x1107 A)) 
                                   (=> 
                                       (MS1 x1106 x1107 s124) 
                                       (and 
                                           (<= 1 x1106) 
                                           (<= x1106 n63)))) 
                               (forall ((x1108 Int) (x1109 A) (x1110 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1108 x1109 s124) 
                                           (MS1 x1108 x1110 s124)) 
                                       (= x1109 x1110))) 
                               (forall ((x1111 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1111) 
                                           (<= x1111 n63)) 
                                       (exists ((x1112 A)) 
                                           (MS1 x1111 x1112 s124)))))) 
                       (exists ((n64 Int)) 
                           (and 
                               (<= 0 n64) 
                               (forall ((x1113 Int) (x1114 A)) 
                                   (=> 
                                       (MS1 x1113 x1114 s224) 
                                       (and 
                                           (<= 1 x1113) 
                                           (<= x1113 n64)))) 
                               (forall ((x1115 Int) (x1116 A) (x1117 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1115 x1116 s224) 
                                           (MS1 x1115 x1117 s224)) 
                                       (= x1116 x1117))) 
                               (forall ((x1118 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1118) 
                                           (<= x1118 n64)) 
                                       (exists ((x1119 A)) 
                                           (MS1 x1118 x1119 s224)))))) 
                       (<= 1 i43) 
                       (forall ((x1120 Int)) 
                           (=> 
                               (length s124 x1120) 
                               (<= i43 x1120)))) 
                   (or 
                       (exists ((i44 Int)) 
                           (and 
                               (<= 1 i44) 
                               (forall ((x1121 Int)) 
                                   (=> 
                                       (length s124 x1121) 
                                       (<= i44 x1121))) 
                               (= i43 i44) 
                               (exists ((x1122 A)) 
                                   (and 
                                       (MS1 i44 x1122 s124) 
                                       (MS1 i43 x1122 s124))))) 
                       (exists ((i45 Int)) 
                           (and 
                               (forall ((x1123 Int)) 
                                   (=> 
                                       (length s124 x1123) 
                                       (<= (+ x1123 1) i45))) 
                               (forall ((x1124 Int) (x1125 Int)) 
                                   (=> 
                                       (and 
                                           (length s124 x1125) 
                                           (length s224 x1124)) 
                                       (<= i45 (+ x1125 x1124)))) 
                               (= i43 i45) 
                               (exists ((x1126 A)) 
                                   (and 
                                       (exists ((x1127 Int)) 
                                           (and 
                                               (forall ((x1128 Int)) 
                                                   (=> 
                                                       (length s124 x1128) 
                                                       (= x1127 (- i45 x1128)))) 
                                               (MS1 x1127 x1126 s224))) 
                                       (MS1 i43 x1126 s124))))))))
         :named hyp92))
(assert (! (forall ((s125 PZA) (s225 PZA) (i46 Int)) 
               (=> 
                   (and 
                       (exists ((n65 Int)) 
                           (and 
                               (<= 0 n65) 
                               (forall ((x1129 Int) (x1130 A)) 
                                   (=> 
                                       (MS1 x1129 x1130 s125) 
                                       (and 
                                           (<= 1 x1129) 
                                           (<= x1129 n65)))) 
                               (forall ((x1131 Int) (x1132 A) (x1133 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1131 x1132 s125) 
                                           (MS1 x1131 x1133 s125)) 
                                       (= x1132 x1133))) 
                               (forall ((x1134 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1134) 
                                           (<= x1134 n65)) 
                                       (exists ((x1135 A)) 
                                           (MS1 x1134 x1135 s125)))))) 
                       (exists ((n66 Int)) 
                           (and 
                               (<= 0 n66) 
                               (forall ((x1136 Int) (x1137 A)) 
                                   (=> 
                                       (MS1 x1136 x1137 s225) 
                                       (and 
                                           (<= 1 x1136) 
                                           (<= x1136 n66)))) 
                               (forall ((x1138 Int) (x1139 A) (x1140 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1138 x1139 s225) 
                                           (MS1 x1138 x1140 s225)) 
                                       (= x1139 x1140))) 
                               (forall ((x1141 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1141) 
                                           (<= x1141 n66)) 
                                       (exists ((x1142 A)) 
                                           (MS1 x1141 x1142 s225)))))) 
                       (forall ((x1143 Int)) 
                           (=> 
                               (length s125 x1143) 
                               (<= (+ x1143 1) i46))) 
                       (forall ((x1144 Int) (x1145 Int)) 
                           (=> 
                               (and 
                                   (length s125 x1145) 
                                   (length s225 x1144)) 
                               (<= i46 (+ x1145 x1144))))) 
                   (or 
                       (exists ((i47 Int)) 
                           (and 
                               (<= 1 i47) 
                               (forall ((x1146 Int)) 
                                   (=> 
                                       (length s125 x1146) 
                                       (<= i47 x1146))) 
                               (= i46 i47) 
                               (exists ((x1147 Int) (x1148 A)) 
                                   (and 
                                       (forall ((x1149 Int)) 
                                           (=> 
                                               (length s125 x1149) 
                                               (= x1147 (- i46 x1149)))) 
                                       (MS1 i47 x1148 s125) 
                                       (MS1 x1147 x1148 s225))))) 
                       (exists ((i48 Int)) 
                           (and 
                               (forall ((x1150 Int)) 
                                   (=> 
                                       (length s125 x1150) 
                                       (<= (+ x1150 1) i48))) 
                               (forall ((x1151 Int) (x1152 Int)) 
                                   (=> 
                                       (and 
                                           (length s125 x1152) 
                                           (length s225 x1151)) 
                                       (<= i48 (+ x1152 x1151)))) 
                               (= i46 i48) 
                               (exists ((x1153 Int) (x1154 A)) 
                                   (and 
                                       (forall ((x1155 Int)) 
                                           (=> 
                                               (length s125 x1155) 
                                               (= x1153 (- i46 x1155)))) 
                                       (exists ((x1156 Int)) 
                                           (and 
                                               (forall ((x1157 Int)) 
                                                   (=> 
                                                       (length s125 x1157) 
                                                       (= x1156 (- i48 x1157)))) 
                                               (MS1 x1156 x1154 s225))) 
                                       (MS1 x1153 x1154 s225))))))))
         :named hyp93))
(assert (! (forall ((s126 PZA) (s226 PZA) (b1 PA)) 
               (=> 
                   (and 
                       (exists ((n67 Int)) 
                           (and 
                               (<= 0 n67) 
                               (forall ((x1158 Int) (x1159 A)) 
                                   (=> 
                                       (MS1 x1158 x1159 s126) 
                                       (and 
                                           (<= 1 x1158) 
                                           (<= x1158 n67)))) 
                               (forall ((x1160 Int) (x1161 A) (x1162 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1160 x1161 s126) 
                                           (MS1 x1160 x1162 s126)) 
                                       (= x1161 x1162))) 
                               (forall ((x1163 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1163) 
                                           (<= x1163 n67)) 
                                       (exists ((x1164 A)) 
                                           (MS1 x1163 x1164 s126)))))) 
                       (exists ((n68 Int)) 
                           (and 
                               (<= 0 n68) 
                               (forall ((x1165 Int) (x1166 A)) 
                                   (=> 
                                       (MS1 x1165 x1166 s226) 
                                       (and 
                                           (<= 1 x1165) 
                                           (<= x1165 n68)))) 
                               (forall ((x1167 Int) (x1168 A) (x1169 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1167 x1168 s226) 
                                           (MS1 x1167 x1169 s226)) 
                                       (= x1168 x1169))) 
                               (forall ((x1170 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1170) 
                                           (<= x1170 n68)) 
                                       (exists ((x1171 A)) 
                                           (MS1 x1170 x1171 s226)))))) 
                       (forall ((x1172 A)) 
                           (=> 
                               (exists ((x1173 Int)) 
                                   (MS1 x1173 x1172 s126)) 
                               (MS0 x1172 b1))) 
                       (forall ((x1174 A)) 
                           (=> 
                               (exists ((x1175 Int)) 
                                   (MS1 x1175 x1174 s226)) 
                               (MS0 x1174 b1)))) 
                   (and 
                       (forall ((x1176 Int) (x1177 A)) 
                           (=> 
                               (or 
                                   (exists ((i49 Int)) 
                                       (and 
                                           (<= 1 i49) 
                                           (forall ((x1178 Int)) 
                                               (=> 
                                                   (length s126 x1178) 
                                                   (<= i49 x1178))) 
                                           (= x1176 i49) 
                                           (MS1 i49 x1177 s126))) 
                                   (exists ((i50 Int)) 
                                       (and 
                                           (forall ((x1179 Int)) 
                                               (=> 
                                                   (length s126 x1179) 
                                                   (<= (+ x1179 1) i50))) 
                                           (forall ((x1180 Int) (x1181 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s126 x1181) 
                                                       (length s226 x1180)) 
                                                   (<= i50 (+ x1181 x1180)))) 
                                           (= x1176 i50) 
                                           (exists ((x1182 Int)) 
                                               (and 
                                                   (forall ((x1183 Int)) 
                                                       (=> 
                                                           (length s126 x1183) 
                                                           (= x1182 (- i50 x1183)))) 
                                                   (MS1 x1182 x1177 s226)))))) 
                               (and 
                                   (<= 1 x1176) 
                                   (forall ((x1184 Int) (x1185 Int)) 
                                       (=> 
                                           (and 
                                               (length s126 x1185) 
                                               (length s226 x1184)) 
                                           (<= x1176 (+ x1185 x1184)))) 
                                   (MS0 x1177 b1)))) 
                       (forall ((x1186 Int) (x1187 A) (x1188 A)) 
                           (=> 
                               (and 
                                   (or 
                                       (exists ((i51 Int)) 
                                           (and 
                                               (<= 1 i51) 
                                               (forall ((x1189 Int)) 
                                                   (=> 
                                                       (length s126 x1189) 
                                                       (<= i51 x1189))) 
                                               (= x1186 i51) 
                                               (MS1 i51 x1187 s126))) 
                                       (exists ((i52 Int)) 
                                           (and 
                                               (forall ((x1190 Int)) 
                                                   (=> 
                                                       (length s126 x1190) 
                                                       (<= (+ x1190 1) i52))) 
                                               (forall ((x1191 Int) (x1192 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s126 x1192) 
                                                           (length s226 x1191)) 
                                                       (<= i52 (+ x1192 x1191)))) 
                                               (= x1186 i52) 
                                               (exists ((x1193 Int)) 
                                                   (and 
                                                       (forall ((x1194 Int)) 
                                                           (=> 
                                                               (length s126 x1194) 
                                                               (= x1193 (- i52 x1194)))) 
                                                       (MS1 x1193 x1187 s226)))))) 
                                   (or 
                                       (exists ((i53 Int)) 
                                           (and 
                                               (<= 1 i53) 
                                               (forall ((x1195 Int)) 
                                                   (=> 
                                                       (length s126 x1195) 
                                                       (<= i53 x1195))) 
                                               (= x1186 i53) 
                                               (MS1 i53 x1188 s126))) 
                                       (exists ((i54 Int)) 
                                           (and 
                                               (forall ((x1196 Int)) 
                                                   (=> 
                                                       (length s126 x1196) 
                                                       (<= (+ x1196 1) i54))) 
                                               (forall ((x1197 Int) (x1198 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s126 x1198) 
                                                           (length s226 x1197)) 
                                                       (<= i54 (+ x1198 x1197)))) 
                                               (= x1186 i54) 
                                               (exists ((x1199 Int)) 
                                                   (and 
                                                       (forall ((x1200 Int)) 
                                                           (=> 
                                                               (length s126 x1200) 
                                                               (= x1199 (- i54 x1200)))) 
                                                       (MS1 x1199 x1188 s226))))))) 
                               (= x1187 x1188))) 
                       (forall ((x1201 Int)) 
                           (=> 
                               (and 
                                   (<= 1 x1201) 
                                   (forall ((x1202 Int) (x1203 Int)) 
                                       (=> 
                                           (and 
                                               (length s126 x1203) 
                                               (length s226 x1202)) 
                                           (<= x1201 (+ x1203 x1202))))) 
                               (or 
                                   (exists ((x1204 A)) 
                                       (exists ((i55 Int)) 
                                           (and 
                                               (<= 1 i55) 
                                               (forall ((x1205 Int)) 
                                                   (=> 
                                                       (length s126 x1205) 
                                                       (<= i55 x1205))) 
                                               (= x1201 i55) 
                                               (MS1 i55 x1204 s126)))) 
                                   (exists ((x1206 A)) 
                                       (exists ((i56 Int)) 
                                           (and 
                                               (forall ((x1207 Int)) 
                                                   (=> 
                                                       (length s126 x1207) 
                                                       (<= (+ x1207 1) i56))) 
                                               (forall ((x1208 Int) (x1209 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length s126 x1209) 
                                                           (length s226 x1208)) 
                                                       (<= i56 (+ x1209 x1208)))) 
                                               (= x1201 i56) 
                                               (exists ((x1210 Int)) 
                                                   (and 
                                                       (forall ((x1211 Int)) 
                                                           (=> 
                                                               (length s126 x1211) 
                                                               (= x1210 (- i56 x1211)))) 
                                                       (MS1 x1210 x1206 s226))))))))))))
         :named hyp94))
(assert (! (forall ((x1212 A) (y30 A)) 
               (=> 
                   (and 
                       (MS0 x1212 a) 
                       (MS0 y30 a)) 
                   (forall ((x1213 PZA)) 
                       (= 
                           (exists ((x1214 A) (x1215 A)) 
                               (and 
                                   (= x1214 y30) 
                                   (= x1215 x1212) 
                                   (path x1214 x1215 x1213))) 
                           (exists ((x1216 PZA)) 
                               (and 
                                   (exists ((x1217 A) (x1218 A)) 
                                       (and 
                                           (= x1217 x1212) 
                                           (= x1218 y30) 
                                           (path x1217 x1218 x1216))) 
                                   (exists ((s48 PZA)) 
                                       (and 
                                           (exists ((n69 Int)) 
                                               (and 
                                                   (<= 0 n69) 
                                                   (forall ((x1219 Int) (x1220 A)) 
                                                       (=> 
                                                           (MS1 x1219 x1220 s48) 
                                                           (and 
                                                               (<= 1 x1219) 
                                                               (<= x1219 n69)))) 
                                                   (forall ((x1221 Int) (x1222 A) (x1223 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS1 x1221 x1222 s48) 
                                                               (MS1 x1221 x1223 s48)) 
                                                           (= x1222 x1223))) 
                                                   (forall ((x1224 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1224) 
                                                               (<= x1224 n69)) 
                                                           (exists ((x1225 A)) 
                                                               (MS1 x1224 x1225 s48)))))) 
                                           (forall ((x1226 Int) (x1227 A)) 
                                               (= 
                                                   (MS1 x1226 x1227 x1216) 
                                                   (MS1 x1226 x1227 s48))) 
                                           (forall ((x1228 Int) (x1229 A)) 
                                               (= 
                                                   (MS1 x1228 x1229 x1213) 
                                                   (exists ((i57 Int)) 
                                                       (and 
                                                           (<= 1 i57) 
                                                           (forall ((x1230 Int)) 
                                                               (=> 
                                                                   (length s48 x1230) 
                                                                   (<= i57 x1230))) 
                                                           (= x1228 i57) 
                                                           (exists ((x1231 Int)) 
                                                               (and 
                                                                   (forall ((x1232 Int)) 
                                                                       (=> 
                                                                           (length s48 x1232) 
                                                                           (= x1231 (+ (- x1232 i57) 1)))) 
                                                                   (MS1 x1231 x1229 s48)))))))))))))))
         :named hyp95))
(assert (! (and 
               (forall ((x1233 PZA) (x1234 PZA)) 
                   (=> 
                       (exists ((s49 PZA)) 
                           (and 
                               (exists ((n70 Int)) 
                                   (and 
                                       (<= 0 n70) 
                                       (forall ((x1235 Int) (x1236 A)) 
                                           (=> 
                                               (MS1 x1235 x1236 s49) 
                                               (and 
                                                   (<= 1 x1235) 
                                                   (<= x1235 n70)))) 
                                       (forall ((x1237 Int) (x1238 A) (x1239 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x1237 x1238 s49) 
                                                   (MS1 x1237 x1239 s49)) 
                                               (= x1238 x1239))) 
                                       (forall ((x1240 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1240) 
                                                   (<= x1240 n70)) 
                                               (exists ((x1241 A)) 
                                                   (MS1 x1240 x1241 s49)))))) 
                               (forall ((x1242 Int) (x1243 A)) 
                                   (= 
                                       (MS1 x1242 x1243 x1233) 
                                       (MS1 x1242 x1243 s49))) 
                               (forall ((x1244 Int) (x1245 A)) 
                                   (= 
                                       (MS1 x1244 x1245 x1234) 
                                       (exists ((i58 Int)) 
                                           (and 
                                               (<= 1 i58) 
                                               (forall ((x1246 Int)) 
                                                   (=> 
                                                       (length s49 x1246) 
                                                       (<= i58 x1246))) 
                                               (= x1244 i58) 
                                               (exists ((x1247 Int)) 
                                                   (and 
                                                       (forall ((x1248 Int)) 
                                                           (=> 
                                                               (length s49 x1248) 
                                                               (= x1247 (+ (- x1248 i58) 1)))) 
                                                       (MS1 x1247 x1245 s49))))))))) 
                       (and 
                           (exists ((s50 PZA)) 
                               (and 
                                   (exists ((n71 Int)) 
                                       (and 
                                           (<= 0 n71) 
                                           (forall ((x1249 Int) (x1250 A)) 
                                               (=> 
                                                   (MS1 x1249 x1250 s50) 
                                                   (and 
                                                       (<= 1 x1249) 
                                                       (<= x1249 n71)))) 
                                           (forall ((x1251 Int) (x1252 A) (x1253 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1251 x1252 s50) 
                                                       (MS1 x1251 x1253 s50)) 
                                                   (= x1252 x1253))) 
                                           (forall ((x1254 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1254) 
                                                       (<= x1254 n71)) 
                                                   (exists ((x1255 A)) 
                                                       (MS1 x1254 x1255 s50)))))) 
                                   (forall ((x1256 Int) (x1257 A)) 
                                       (= 
                                           (MS1 x1256 x1257 x1233) 
                                           (MS1 x1256 x1257 s50))))) 
                           (exists ((s51 PZA)) 
                               (and 
                                   (exists ((n72 Int)) 
                                       (and 
                                           (<= 0 n72) 
                                           (forall ((x1258 Int) (x1259 A)) 
                                               (=> 
                                                   (MS1 x1258 x1259 s51) 
                                                   (and 
                                                       (<= 1 x1258) 
                                                       (<= x1258 n72)))) 
                                           (forall ((x1260 Int) (x1261 A) (x1262 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1260 x1261 s51) 
                                                       (MS1 x1260 x1262 s51)) 
                                                   (= x1261 x1262))) 
                                           (forall ((x1263 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1263) 
                                                       (<= x1263 n72)) 
                                                   (exists ((x1264 A)) 
                                                       (MS1 x1263 x1264 s51)))))) 
                                   (forall ((x1265 Int) (x1266 A)) 
                                       (= 
                                           (MS1 x1265 x1266 x1234) 
                                           (MS1 x1265 x1266 s51)))))))) 
               (forall ((x1267 PZA) (x1268 PZA) (x1269 PZA)) 
                   (=> 
                       (and 
                           (exists ((s52 PZA)) 
                               (and 
                                   (exists ((n73 Int)) 
                                       (and 
                                           (<= 0 n73) 
                                           (forall ((x1270 Int) (x1271 A)) 
                                               (=> 
                                                   (MS1 x1270 x1271 s52) 
                                                   (and 
                                                       (<= 1 x1270) 
                                                       (<= x1270 n73)))) 
                                           (forall ((x1272 Int) (x1273 A) (x1274 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1272 x1273 s52) 
                                                       (MS1 x1272 x1274 s52)) 
                                                   (= x1273 x1274))) 
                                           (forall ((x1275 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1275) 
                                                       (<= x1275 n73)) 
                                                   (exists ((x1276 A)) 
                                                       (MS1 x1275 x1276 s52)))))) 
                                   (forall ((x1277 Int) (x1278 A)) 
                                       (= 
                                           (MS1 x1277 x1278 x1267) 
                                           (MS1 x1277 x1278 s52))) 
                                   (forall ((x1279 Int) (x1280 A)) 
                                       (= 
                                           (MS1 x1279 x1280 x1268) 
                                           (exists ((i59 Int)) 
                                               (and 
                                                   (<= 1 i59) 
                                                   (forall ((x1281 Int)) 
                                                       (=> 
                                                           (length s52 x1281) 
                                                           (<= i59 x1281))) 
                                                   (= x1279 i59) 
                                                   (exists ((x1282 Int)) 
                                                       (and 
                                                           (forall ((x1283 Int)) 
                                                               (=> 
                                                                   (length s52 x1283) 
                                                                   (= x1282 (+ (- x1283 i59) 1)))) 
                                                           (MS1 x1282 x1280 s52))))))))) 
                           (exists ((s53 PZA)) 
                               (and 
                                   (exists ((n74 Int)) 
                                       (and 
                                           (<= 0 n74) 
                                           (forall ((x1284 Int) (x1285 A)) 
                                               (=> 
                                                   (MS1 x1284 x1285 s53) 
                                                   (and 
                                                       (<= 1 x1284) 
                                                       (<= x1284 n74)))) 
                                           (forall ((x1286 Int) (x1287 A) (x1288 A)) 
                                               (=> 
                                                   (and 
                                                       (MS1 x1286 x1287 s53) 
                                                       (MS1 x1286 x1288 s53)) 
                                                   (= x1287 x1288))) 
                                           (forall ((x1289 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 x1289) 
                                                       (<= x1289 n74)) 
                                                   (exists ((x1290 A)) 
                                                       (MS1 x1289 x1290 s53)))))) 
                                   (forall ((x1291 Int) (x1292 A)) 
                                       (= 
                                           (MS1 x1291 x1292 x1267) 
                                           (MS1 x1291 x1292 s53))) 
                                   (forall ((x1293 Int) (x1294 A)) 
                                       (= 
                                           (MS1 x1293 x1294 x1269) 
                                           (exists ((i60 Int)) 
                                               (and 
                                                   (<= 1 i60) 
                                                   (forall ((x1295 Int)) 
                                                       (=> 
                                                           (length s53 x1295) 
                                                           (<= i60 x1295))) 
                                                   (= x1293 i60) 
                                                   (exists ((x1296 Int)) 
                                                       (and 
                                                           (forall ((x1297 Int)) 
                                                               (=> 
                                                                   (length s53 x1297) 
                                                                   (= x1296 (+ (- x1297 i60) 1)))) 
                                                           (MS1 x1296 x1294 s53)))))))))) 
                       (forall ((x1298 Int) (x1299 A)) 
                           (= 
                               (MS1 x1298 x1299 x1268) 
                               (MS1 x1298 x1299 x1269))))) 
               (forall ((x1300 PZA)) 
                   (=> 
                       (exists ((s54 PZA)) 
                           (and 
                               (exists ((n75 Int)) 
                                   (and 
                                       (<= 0 n75) 
                                       (forall ((x1301 Int) (x1302 A)) 
                                           (=> 
                                               (MS1 x1301 x1302 s54) 
                                               (and 
                                                   (<= 1 x1301) 
                                                   (<= x1301 n75)))) 
                                       (forall ((x1303 Int) (x1304 A) (x1305 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x1303 x1304 s54) 
                                                   (MS1 x1303 x1305 s54)) 
                                               (= x1304 x1305))) 
                                       (forall ((x1306 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1306) 
                                                   (<= x1306 n75)) 
                                               (exists ((x1307 A)) 
                                                   (MS1 x1306 x1307 s54)))))) 
                               (forall ((x1308 Int) (x1309 A)) 
                                   (= 
                                       (MS1 x1308 x1309 x1300) 
                                       (MS1 x1308 x1309 s54))))) 
                       (exists ((x1310 PZA) (s55 PZA)) 
                           (and 
                               (exists ((n76 Int)) 
                                   (and 
                                       (<= 0 n76) 
                                       (forall ((x1311 Int) (x1312 A)) 
                                           (=> 
                                               (MS1 x1311 x1312 s55) 
                                               (and 
                                                   (<= 1 x1311) 
                                                   (<= x1311 n76)))) 
                                       (forall ((x1313 Int) (x1314 A) (x1315 A)) 
                                           (=> 
                                               (and 
                                                   (MS1 x1313 x1314 s55) 
                                                   (MS1 x1313 x1315 s55)) 
                                               (= x1314 x1315))) 
                                       (forall ((x1316 Int)) 
                                           (=> 
                                               (and 
                                                   (<= 1 x1316) 
                                                   (<= x1316 n76)) 
                                               (exists ((x1317 A)) 
                                                   (MS1 x1316 x1317 s55)))))) 
                               (forall ((x1318 Int) (x1319 A)) 
                                   (= 
                                       (MS1 x1318 x1319 x1300) 
                                       (MS1 x1318 x1319 s55))) 
                               (forall ((x1320 Int) (x1321 A)) 
                                   (= 
                                       (MS1 x1320 x1321 x1310) 
                                       (exists ((i61 Int)) 
                                           (and 
                                               (<= 1 i61) 
                                               (forall ((x1322 Int)) 
                                                   (=> 
                                                       (length s55 x1322) 
                                                       (<= i61 x1322))) 
                                               (= x1320 i61) 
                                               (exists ((x1323 Int)) 
                                                   (and 
                                                       (forall ((x1324 Int)) 
                                                           (=> 
                                                               (length s55 x1324) 
                                                               (= x1323 (+ (- x1324 i61) 1)))) 
                                                       (MS1 x1323 x1321 s55))))))))))))
         :named hyp96))
(assert (! (forall ((x1325 A) (y31 A) (p23 PZA)) 
               (=> 
                   (path x1325 y31 p23) 
                   (exists ((x1326 PZA)) 
                       (and 
                           (forall ((x1327 Int) (x1328 A)) 
                               (= 
                                   (MS1 x1327 x1328 x1326) 
                                   (exists ((i62 Int)) 
                                       (and 
                                           (<= 1 i62) 
                                           (forall ((x1329 Int)) 
                                               (=> 
                                                   (length p23 x1329) 
                                                   (<= i62 x1329))) 
                                           (= x1327 i62) 
                                           (exists ((x1330 Int)) 
                                               (and 
                                                   (forall ((x1331 Int)) 
                                                       (=> 
                                                           (length p23 x1331) 
                                                           (= x1330 (+ (- x1331 i62) 1)))) 
                                                   (MS1 x1330 x1328 p23))))))) 
                           (path y31 x1325 x1326)))))
         :named hyp97))
(assert (! (forall ((x1332 A) (y210 A) (p24 PZA)) 
               (=> 
                   (and 
                       (MS0 x1332 a) 
                       (MS0 y210 a) 
                       (path x1332 y210 p24) 
                       (forall ((x1333 Int)) 
                           (=> 
                               (length p24 x1333) 
                               (<= 3 x1333)))) 
                   (exists ((x1334 A) (x1335 PZA)) 
                       (and 
                           (exists ((x1336 Int)) 
                               (and 
                                   (forall ((x1337 Int) (x1338 Int)) 
                                       (=> 
                                           (and 
                                               (length p24 x1338) 
                                               (length p24 x1337)) 
                                           (= x1336 (+ (- x1338 (- x1337 1)) 1)))) 
                                   (MS1 x1336 x1334 p24))) 
                           (forall ((x1339 Int) (x1340 A)) 
                               (= 
                                   (MS1 x1339 x1340 x1335) 
                                   (and 
                                       (exists ((i63 Int)) 
                                           (and 
                                               (<= 1 i63) 
                                               (forall ((x1341 Int)) 
                                                   (=> 
                                                       (length p24 x1341) 
                                                       (<= i63 x1341))) 
                                               (= x1339 i63) 
                                               (exists ((x1342 Int)) 
                                                   (and 
                                                       (forall ((x1343 Int)) 
                                                           (=> 
                                                               (length p24 x1343) 
                                                               (= x1342 (+ (- x1343 i63) 1)))) 
                                                       (MS1 x1342 x1340 p24))))) 
                                       (<= 1 x1339) 
                                       (forall ((x1344 Int)) 
                                           (=> 
                                               (length p24 x1344) 
                                               (<= x1339 (- x1344 1))))))) 
                           (path y210 x1334 x1335)))))
         :named hyp98))
(assert (! (forall ((s56 PZA)) 
               (=> 
                   (exists ((n77 Int)) 
                       (and 
                           (<= 0 n77) 
                           (forall ((x1345 Int) (x1346 A)) 
                               (=> 
                                   (MS1 x1345 x1346 s56) 
                                   (and 
                                       (<= 1 x1345) 
                                       (<= x1345 n77)))) 
                           (forall ((x1347 Int) (x1348 A) (x1349 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1347 x1348 s56) 
                                       (MS1 x1347 x1349 s56)) 
                                   (= x1348 x1349))) 
                           (forall ((x1350 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1350) 
                                       (<= x1350 n77)) 
                                   (exists ((x1351 A)) 
                                       (MS1 x1350 x1351 s56)))))) 
                   (exists ((x1352 PZA) (x1353 Int)) 
                       (and 
                           (forall ((x1354 Int) (x1355 A)) 
                               (= 
                                   (MS1 x1354 x1355 x1352) 
                                   (exists ((i64 Int)) 
                                       (and 
                                           (<= 1 i64) 
                                           (forall ((x1356 Int)) 
                                               (=> 
                                                   (length s56 x1356) 
                                                   (<= i64 x1356))) 
                                           (= x1354 i64) 
                                           (exists ((x1357 Int)) 
                                               (and 
                                                   (forall ((x1358 Int)) 
                                                       (=> 
                                                           (length s56 x1358) 
                                                           (= x1357 (+ (- x1358 i64) 1)))) 
                                                   (MS1 x1357 x1355 s56))))))) 
                           (length s56 x1353) 
                           (length x1352 x1353)))))
         :named hyp99))
(assert (! (forall ((s57 PZA)) 
               (=> 
                   (exists ((n78 Int)) 
                       (and 
                           (<= 0 n78) 
                           (forall ((x1359 Int) (x1360 A)) 
                               (=> 
                                   (MS1 x1359 x1360 s57) 
                                   (and 
                                       (<= 1 x1359) 
                                       (<= x1359 n78)))) 
                           (forall ((x1361 Int) (x1362 A) (x1363 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1361 x1362 s57) 
                                       (MS1 x1361 x1363 s57)) 
                                   (= x1362 x1363))) 
                           (forall ((x1364 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1364) 
                                       (<= x1364 n78)) 
                                   (exists ((x1365 A)) 
                                       (MS1 x1364 x1365 s57)))))) 
                   (forall ((x1366 A)) 
                       (= 
                           (exists ((i65 Int)) 
                               (and 
                                   (<= 1 i65) 
                                   (forall ((x1367 Int)) 
                                       (=> 
                                           (length s57 x1367) 
                                           (<= i65 x1367))) 
                                   (exists ((x1368 Int)) 
                                       (and 
                                           (forall ((x1369 Int)) 
                                               (=> 
                                                   (length s57 x1369) 
                                                   (= x1368 (+ (- x1369 i65) 1)))) 
                                           (MS1 x1368 x1366 s57))))) 
                           (exists ((x1370 Int)) 
                               (MS1 x1370 x1366 s57))))))
         :named hyp100))
(assert (! (forall ((s58 PZA)) 
               (=> 
                   (exists ((n79 Int)) 
                       (and 
                           (<= 0 n79) 
                           (forall ((x1371 Int) (x1372 A)) 
                               (=> 
                                   (MS1 x1371 x1372 s58) 
                                   (and 
                                       (<= 1 x1371) 
                                       (<= x1371 n79)))) 
                           (forall ((x1373 Int) (x1374 A) (x1375 A)) 
                               (=> 
                                   (and 
                                       (MS1 x1373 x1374 s58) 
                                       (MS1 x1373 x1375 s58)) 
                                   (= x1374 x1375))) 
                           (forall ((x1376 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 x1376) 
                                       (<= x1376 n79)) 
                                   (exists ((x1377 A)) 
                                       (MS1 x1376 x1377 s58)))))) 
                   (forall ((x1378 Int) (x1379 A)) 
                       (= 
                           (exists ((i66 Int)) 
                               (and 
                                   (<= 1 i66) 
                                   (forall ((x1380 Int)) 
                                       (=> 
                                           (exists ((x1381 PZA)) 
                                               (and 
                                                   (forall ((x1382 Int) (x1383 A)) 
                                                       (= 
                                                           (MS1 x1382 x1383 x1381) 
                                                           (exists ((i67 Int)) 
                                                               (and 
                                                                   (<= 1 i67) 
                                                                   (forall ((x1384 Int)) 
                                                                       (=> 
                                                                           (length s58 x1384) 
                                                                           (<= i67 x1384))) 
                                                                   (= x1382 i67) 
                                                                   (exists ((x1385 Int)) 
                                                                       (and 
                                                                           (forall ((x1386 Int)) 
                                                                               (=> 
                                                                                   (length s58 x1386) 
                                                                                   (= x1385 (+ (- x1386 i67) 1)))) 
                                                                           (MS1 x1385 x1383 s58))))))) 
                                                   (length x1381 x1380))) 
                                           (<= i66 x1380))) 
                                   (= x1378 i66) 
                                   (exists ((x1387 Int)) 
                                       (and 
                                           (forall ((x1388 Int) (x1389 Int)) 
                                               (=> 
                                                   (and 
                                                       (length s58 x1389) 
                                                       (exists ((x1390 PZA)) 
                                                           (and 
                                                               (forall ((x1391 Int) (x1392 A)) 
                                                                   (= 
                                                                       (MS1 x1391 x1392 x1390) 
                                                                       (exists ((i68 Int)) 
                                                                           (and 
                                                                               (<= 1 i68) 
                                                                               (forall ((x1393 Int)) 
                                                                                   (=> 
                                                                                       (length s58 x1393) 
                                                                                       (<= i68 x1393))) 
                                                                               (= x1391 i68) 
                                                                               (exists ((x1394 Int)) 
                                                                                   (and 
                                                                                       (forall ((x1395 Int)) 
                                                                                           (=> 
                                                                                               (length s58 x1395) 
                                                                                               (= x1394 (+ (- x1395 i68) 1)))) 
                                                                                       (MS1 x1394 x1392 s58))))))) 
                                                               (length x1390 x1388)))) 
                                                   (= x1387 (+ (- x1389 (+ (- x1388 i66) 1)) 1)))) 
                                           (MS1 x1387 x1379 s58))))) 
                           (MS1 x1378 x1379 s58)))))
         :named hyp101))
(assert (! (forall ((x1396 A) (y32 A)) 
               (=> 
                   (and 
                       (MS0 x1396 a) 
                       (MS0 y32 a)) 
                   (exists ((x1397 Int)) 
                       (and 
                           (exists ((x1398 PZA)) 
                               (and 
                                   (exists ((x1399 A) (x1400 A)) 
                                       (and 
                                           (= x1399 x1396) 
                                           (= x1400 y32) 
                                           (exists ((x1401 A) (y33 A) (p25 PZA)) 
                                               (and 
                                                   (exists ((n80 Int)) 
                                                       (and 
                                                           (<= 0 n80) 
                                                           (forall ((x1402 Int) (x1403 A)) 
                                                               (=> 
                                                                   (MS1 x1402 x1403 p25) 
                                                                   (and 
                                                                       (<= 1 x1402) 
                                                                       (<= x1402 n80)))) 
                                                           (forall ((x1404 Int) (x1405 A) (x1406 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS1 x1404 x1405 p25) 
                                                                       (MS1 x1404 x1406 p25)) 
                                                                   (= x1405 x1406))) 
                                                           (forall ((x1407 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x1407) 
                                                                       (<= x1407 n80)) 
                                                                   (exists ((x1408 A)) 
                                                                       (MS1 x1407 x1408 p25)))))) 
                                                   (forall ((x1409 A)) 
                                                       (=> 
                                                           (exists ((x1410 Int)) 
                                                               (MS1 x1410 x1409 p25)) 
                                                           (MS0 x1409 a))) 
                                                   (forall ((x1411 Int)) 
                                                       (=> 
                                                           (length p25 x1411) 
                                                           (< 1 x1411))) 
                                                   (exists ((x1412 Int)) 
                                                       (and 
                                                           (= x1412 1) 
                                                           (MS1 x1412 x1401 p25))) 
                                                   (exists ((x1413 Int)) 
                                                       (and 
                                                           (length p25 x1413) 
                                                           (MS1 x1413 y33 p25))) 
                                                   (forall ((i69 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i69) 
                                                               (forall ((x1414 Int)) 
                                                                   (=> 
                                                                       (length p25 x1414) 
                                                                       (<= i69 (- x1414 1))))) 
                                                           (exists ((x1415 A) (x1416 A)) 
                                                               (and 
                                                                   (MS1 i69 x1415 p25) 
                                                                   (exists ((x1417 Int)) 
                                                                       (and 
                                                                           (= x1417 (+ i69 1)) 
                                                                           (MS1 x1417 x1416 p25))) 
                                                                   (MS x1415 x1416 r))))) 
                                                   (= x1399 x1401) 
                                                   (= x1400 y33) 
                                                   (forall ((x1418 Int) (x1419 A)) 
                                                       (= 
                                                           (MS1 x1418 x1419 x1398) 
                                                           (MS1 x1418 x1419 p25))))))) 
                                   (length x1398 x1397))) 
                           (forall ((x1420 Int)) 
                               (=> 
                                   (exists ((x1421 PZA)) 
                                       (and 
                                           (exists ((x1422 A) (x1423 A)) 
                                               (and 
                                                   (= x1422 x1396) 
                                                   (= x1423 y32) 
                                                   (exists ((x1424 A) (y34 A) (p26 PZA)) 
                                                       (and 
                                                           (exists ((n81 Int)) 
                                                               (and 
                                                                   (<= 0 n81) 
                                                                   (forall ((x1425 Int) (x1426 A)) 
                                                                       (=> 
                                                                           (MS1 x1425 x1426 p26) 
                                                                           (and 
                                                                               (<= 1 x1425) 
                                                                               (<= x1425 n81)))) 
                                                                   (forall ((x1427 Int) (x1428 A) (x1429 A)) 
                                                                       (=> 
                                                                           (and 
                                                                               (MS1 x1427 x1428 p26) 
                                                                               (MS1 x1427 x1429 p26)) 
                                                                           (= x1428 x1429))) 
                                                                   (forall ((x1430 Int)) 
                                                                       (=> 
                                                                           (and 
                                                                               (<= 1 x1430) 
                                                                               (<= x1430 n81)) 
                                                                           (exists ((x1431 A)) 
                                                                               (MS1 x1430 x1431 p26)))))) 
                                                           (forall ((x1432 A)) 
                                                               (=> 
                                                                   (exists ((x1433 Int)) 
                                                                       (MS1 x1433 x1432 p26)) 
                                                                   (MS0 x1432 a))) 
                                                           (forall ((x1434 Int)) 
                                                               (=> 
                                                                   (length p26 x1434) 
                                                                   (< 1 x1434))) 
                                                           (exists ((x1435 Int)) 
                                                               (and 
                                                                   (= x1435 1) 
                                                                   (MS1 x1435 x1424 p26))) 
                                                           (exists ((x1436 Int)) 
                                                               (and 
                                                                   (length p26 x1436) 
                                                                   (MS1 x1436 y34 p26))) 
                                                           (forall ((i70 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 i70) 
                                                                       (forall ((x1437 Int)) 
                                                                           (=> 
                                                                               (length p26 x1437) 
                                                                               (<= i70 (- x1437 1))))) 
                                                                   (exists ((x1438 A) (x1439 A)) 
                                                                       (and 
                                                                           (MS1 i70 x1438 p26) 
                                                                           (exists ((x1440 Int)) 
                                                                               (and 
                                                                                   (= x1440 (+ i70 1)) 
                                                                                   (MS1 x1440 x1439 p26))) 
                                                                           (MS x1438 x1439 r))))) 
                                                           (= x1422 x1424) 
                                                           (= x1423 y34) 
                                                           (forall ((x1441 Int) (x1442 A)) 
                                                               (= 
                                                                   (MS1 x1441 x1442 x1421) 
                                                                   (MS1 x1441 x1442 p26))))))) 
                                           (length x1421 x1420))) 
                                   (<= x1397 x1420))) 
                           (dist x1396 y32 x1397)))))
         :named hyp102))
(assert (! (forall ((x1443 A) (y35 A)) 
               (=> 
                   (and 
                       (MS0 x1443 a) 
                       (MS0 y35 a)) 
                   (forall ((x1444 PZA)) 
                       (= 
                           (exists ((x1445 A) (x1446 A)) 
                               (and 
                                   (= x1445 y35) 
                                   (= x1446 x1443) 
                                   (exists ((x1447 A) (y36 A) (p27 PZA)) 
                                       (and 
                                           (exists ((n82 Int)) 
                                               (and 
                                                   (<= 0 n82) 
                                                   (forall ((x1448 Int) (x1449 A)) 
                                                       (=> 
                                                           (MS1 x1448 x1449 p27) 
                                                           (and 
                                                               (<= 1 x1448) 
                                                               (<= x1448 n82)))) 
                                                   (forall ((x1450 Int) (x1451 A) (x1452 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS1 x1450 x1451 p27) 
                                                               (MS1 x1450 x1452 p27)) 
                                                           (= x1451 x1452))) 
                                                   (forall ((x1453 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1453) 
                                                               (<= x1453 n82)) 
                                                           (exists ((x1454 A)) 
                                                               (MS1 x1453 x1454 p27)))))) 
                                           (forall ((x1455 A)) 
                                               (=> 
                                                   (exists ((x1456 Int)) 
                                                       (MS1 x1456 x1455 p27)) 
                                                   (MS0 x1455 a))) 
                                           (forall ((x1457 Int)) 
                                               (=> 
                                                   (length p27 x1457) 
                                                   (< 1 x1457))) 
                                           (exists ((x1458 Int)) 
                                               (and 
                                                   (= x1458 1) 
                                                   (MS1 x1458 x1447 p27))) 
                                           (exists ((x1459 Int)) 
                                               (and 
                                                   (length p27 x1459) 
                                                   (MS1 x1459 y36 p27))) 
                                           (forall ((i71 Int)) 
                                               (=> 
                                                   (and 
                                                       (<= 1 i71) 
                                                       (forall ((x1460 Int)) 
                                                           (=> 
                                                               (length p27 x1460) 
                                                               (<= i71 (- x1460 1))))) 
                                                   (exists ((x1461 A) (x1462 A)) 
                                                       (and 
                                                           (MS1 i71 x1461 p27) 
                                                           (exists ((x1463 Int)) 
                                                               (and 
                                                                   (= x1463 (+ i71 1)) 
                                                                   (MS1 x1463 x1462 p27))) 
                                                           (MS x1461 x1462 r))))) 
                                           (= x1445 x1447) 
                                           (= x1446 y36) 
                                           (forall ((x1464 Int) (x1465 A)) 
                                               (= 
                                                   (MS1 x1464 x1465 x1444) 
                                                   (MS1 x1464 x1465 p27))))))) 
                           (exists ((x1466 PZA)) 
                               (and 
                                   (exists ((x1467 A) (x1468 A)) 
                                       (and 
                                           (= x1467 x1443) 
                                           (= x1468 y35) 
                                           (exists ((x1469 A) (y37 A) (p28 PZA)) 
                                               (and 
                                                   (exists ((n83 Int)) 
                                                       (and 
                                                           (<= 0 n83) 
                                                           (forall ((x1470 Int) (x1471 A)) 
                                                               (=> 
                                                                   (MS1 x1470 x1471 p28) 
                                                                   (and 
                                                                       (<= 1 x1470) 
                                                                       (<= x1470 n83)))) 
                                                           (forall ((x1472 Int) (x1473 A) (x1474 A)) 
                                                               (=> 
                                                                   (and 
                                                                       (MS1 x1472 x1473 p28) 
                                                                       (MS1 x1472 x1474 p28)) 
                                                                   (= x1473 x1474))) 
                                                           (forall ((x1475 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (<= 1 x1475) 
                                                                       (<= x1475 n83)) 
                                                                   (exists ((x1476 A)) 
                                                                       (MS1 x1475 x1476 p28)))))) 
                                                   (forall ((x1477 A)) 
                                                       (=> 
                                                           (exists ((x1478 Int)) 
                                                               (MS1 x1478 x1477 p28)) 
                                                           (MS0 x1477 a))) 
                                                   (forall ((x1479 Int)) 
                                                       (=> 
                                                           (length p28 x1479) 
                                                           (< 1 x1479))) 
                                                   (exists ((x1480 Int)) 
                                                       (and 
                                                           (= x1480 1) 
                                                           (MS1 x1480 x1469 p28))) 
                                                   (exists ((x1481 Int)) 
                                                       (and 
                                                           (length p28 x1481) 
                                                           (MS1 x1481 y37 p28))) 
                                                   (forall ((i72 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 i72) 
                                                               (forall ((x1482 Int)) 
                                                                   (=> 
                                                                       (length p28 x1482) 
                                                                       (<= i72 (- x1482 1))))) 
                                                           (exists ((x1483 A) (x1484 A)) 
                                                               (and 
                                                                   (MS1 i72 x1483 p28) 
                                                                   (exists ((x1485 Int)) 
                                                                       (and 
                                                                           (= x1485 (+ i72 1)) 
                                                                           (MS1 x1485 x1484 p28))) 
                                                                   (MS x1483 x1484 r))))) 
                                                   (= x1467 x1469) 
                                                   (= x1468 y37) 
                                                   (forall ((x1486 Int) (x1487 A)) 
                                                       (= 
                                                           (MS1 x1486 x1487 x1466) 
                                                           (MS1 x1486 x1487 p28))))))) 
                                   (exists ((s59 PZA)) 
                                       (and 
                                           (exists ((n84 Int)) 
                                               (and 
                                                   (<= 0 n84) 
                                                   (forall ((x1488 Int) (x1489 A)) 
                                                       (=> 
                                                           (MS1 x1488 x1489 s59) 
                                                           (and 
                                                               (<= 1 x1488) 
                                                               (<= x1488 n84)))) 
                                                   (forall ((x1490 Int) (x1491 A) (x1492 A)) 
                                                       (=> 
                                                           (and 
                                                               (MS1 x1490 x1491 s59) 
                                                               (MS1 x1490 x1492 s59)) 
                                                           (= x1491 x1492))) 
                                                   (forall ((x1493 Int)) 
                                                       (=> 
                                                           (and 
                                                               (<= 1 x1493) 
                                                               (<= x1493 n84)) 
                                                           (exists ((x1494 A)) 
                                                               (MS1 x1493 x1494 s59)))))) 
                                           (forall ((x1495 Int) (x1496 A)) 
                                               (= 
                                                   (MS1 x1495 x1496 x1466) 
                                                   (MS1 x1495 x1496 s59))) 
                                           (forall ((x1497 Int) (x1498 A)) 
                                               (= 
                                                   (MS1 x1497 x1498 x1444) 
                                                   (exists ((i73 Int)) 
                                                       (and 
                                                           (<= 1 i73) 
                                                           (forall ((x1499 Int)) 
                                                               (=> 
                                                                   (length s59 x1499) 
                                                                   (<= i73 x1499))) 
                                                           (= x1497 i73) 
                                                           (exists ((x1500 Int)) 
                                                               (and 
                                                                   (forall ((x1501 Int)) 
                                                                       (=> 
                                                                           (length s59 x1501) 
                                                                           (= x1500 (+ (- x1501 i73) 1)))) 
                                                                   (MS1 x1500 x1498 s59)))))))))))))))
         :named hyp103))
(assert (! (forall ((x1502 A) (x1503 A) (x1504 PZA)) 
               (= 
                   (shpath x1502 x1503 x1504) 
                   (exists ((x1505 A) (y38 A) (p29 PZA)) 
                       (and 
                           (exists ((n85 Int)) 
                               (and 
                                   (<= 0 n85) 
                                   (forall ((x1506 Int) (x1507 A)) 
                                       (=> 
                                           (MS1 x1506 x1507 p29) 
                                           (and 
                                               (<= 1 x1506) 
                                               (<= x1506 n85)))) 
                                   (forall ((x1508 Int) (x1509 A) (x1510 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x1508 x1509 p29) 
                                               (MS1 x1508 x1510 p29)) 
                                           (= x1509 x1510))) 
                                   (forall ((x1511 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1511) 
                                               (<= x1511 n85)) 
                                           (exists ((x1512 A)) 
                                               (MS1 x1511 x1512 p29)))))) 
                           (forall ((x1513 A)) 
                               (=> 
                                   (exists ((x1514 Int)) 
                                       (MS1 x1514 x1513 p29)) 
                                   (MS0 x1513 a))) 
                           (forall ((x1515 Int)) 
                               (=> 
                                   (length p29 x1515) 
                                   (< 1 x1515))) 
                           (exists ((x1516 Int)) 
                               (and 
                                   (= x1516 1) 
                                   (MS1 x1516 x1505 p29))) 
                           (exists ((x1517 Int)) 
                               (and 
                                   (length p29 x1517) 
                                   (MS1 x1517 y38 p29))) 
                           (forall ((i74 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i74) 
                                       (forall ((x1518 Int)) 
                                           (=> 
                                               (length p29 x1518) 
                                               (<= i74 (- x1518 1))))) 
                                   (exists ((x1519 A) (x1520 A)) 
                                       (and 
                                           (MS1 i74 x1519 p29) 
                                           (exists ((x1521 Int)) 
                                               (and 
                                                   (= x1521 (+ i74 1)) 
                                                   (MS1 x1521 x1520 p29))) 
                                           (MS x1519 x1520 r))))) 
                           (exists ((x1522 Int)) 
                               (and 
                                   (length p29 x1522) 
                                   (dist x1505 y38 x1522))) 
                           (= x1502 x1505) 
                           (= x1503 y38) 
                           (forall ((x1523 Int) (x1524 A)) 
                               (= 
                                   (MS1 x1523 x1524 x1504) 
                                   (MS1 x1523 x1524 p29)))))))
         :named hyp104))
(assert (! (forall ((x1525 A) (y39 A) (p30 PZA) (i75 Int)) 
               (=> 
                   (and 
                       (MS0 x1525 a) 
                       (MS0 y39 a) 
                       (exists ((n86 Int)) 
                           (and 
                               (<= 0 n86) 
                               (forall ((x1526 Int) (x1527 A)) 
                                   (=> 
                                       (MS1 x1526 x1527 p30) 
                                       (and 
                                           (<= 1 x1526) 
                                           (<= x1526 n86)))) 
                               (forall ((x1528 Int) (x1529 A) (x1530 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1528 x1529 p30) 
                                           (MS1 x1528 x1530 p30)) 
                                       (= x1529 x1530))) 
                               (forall ((x1531 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1531) 
                                           (<= x1531 n86)) 
                                       (exists ((x1532 A)) 
                                           (MS1 x1531 x1532 p30)))))) 
                       (forall ((x1533 A)) 
                           (=> 
                               (exists ((x1534 Int)) 
                                   (MS1 x1534 x1533 p30)) 
                               (MS0 x1533 a))) 
                       (forall ((x1535 Int)) 
                           (=> 
                               (length p30 x1535) 
                               (< 1 x1535))) 
                       (exists ((x1536 Int)) 
                           (and 
                               (= x1536 1) 
                               (MS1 x1536 x1525 p30))) 
                       (exists ((x1537 Int)) 
                           (and 
                               (length p30 x1537) 
                               (MS1 x1537 y39 p30))) 
                       (forall ((i76 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i76) 
                                   (forall ((x1538 Int)) 
                                       (=> 
                                           (length p30 x1538) 
                                           (<= i76 (- x1538 1))))) 
                               (exists ((x1539 A) (x1540 A)) 
                                   (and 
                                       (MS1 i76 x1539 p30) 
                                       (exists ((x1541 Int)) 
                                           (and 
                                               (= x1541 (+ i76 1)) 
                                               (MS1 x1541 x1540 p30))) 
                                       (MS x1539 x1540 r))))) 
                       (<= 2 i75) 
                       (forall ((x1542 Int)) 
                           (=> 
                               (length p30 x1542) 
                               (<= i75 (- x1542 1))))) 
                   (and 
                       (exists ((n87 Int)) 
                           (and 
                               (<= 0 n87) 
                               (forall ((x1543 Int) (x1544 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1543 x1544 p30) 
                                           (<= 1 x1543) 
                                           (<= x1543 i75)) 
                                       (and 
                                           (<= 1 x1543) 
                                           (<= x1543 n87)))) 
                               (forall ((x1545 Int) (x1546 A) (x1547 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1545 x1546 p30) 
                                           (<= 1 x1545) 
                                           (<= x1545 i75) 
                                           (MS1 x1545 x1547 p30)) 
                                       (= x1546 x1547))) 
                               (forall ((x1548 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1548) 
                                           (<= x1548 n87)) 
                                       (exists ((x1549 A)) 
                                           (and 
                                               (MS1 x1548 x1549 p30) 
                                               (<= 1 x1548) 
                                               (<= x1548 i75))))))) 
                       (forall ((x1550 A)) 
                           (=> 
                               (exists ((x1551 Int)) 
                                   (and 
                                       (MS1 x1551 x1550 p30) 
                                       (<= 1 x1551) 
                                       (<= x1551 i75))) 
                               (MS0 x1550 a))) 
                       (forall ((x1552 Int)) 
                           (=> 
                               (exists ((x1553 PZA)) 
                                   (and 
                                       (forall ((x1554 Int) (x1555 A)) 
                                           (= 
                                               (MS1 x1554 x1555 x1553) 
                                               (and 
                                                   (MS1 x1554 x1555 p30) 
                                                   (<= 1 x1554) 
                                                   (<= x1554 i75)))) 
                                       (length x1553 x1552))) 
                               (< 1 x1552))) 
                       (exists ((x1556 Int)) 
                           (and 
                               (= x1556 1) 
                               (MS1 x1556 x1525 p30))) 
                       (<= 1 1) 
                       (<= 1 i75) 
                       (exists ((x1557 Int) (x1558 A)) 
                           (and 
                               (exists ((x1559 PZA)) 
                                   (and 
                                       (forall ((x1560 Int) (x1561 A)) 
                                           (= 
                                               (MS1 x1560 x1561 x1559) 
                                               (and 
                                                   (MS1 x1560 x1561 p30) 
                                                   (<= 1 x1560) 
                                                   (<= x1560 i75)))) 
                                       (length x1559 x1557))) 
                               (MS1 i75 x1558 p30) 
                               (MS1 x1557 x1558 p30))) 
                       (forall ((x1562 Int)) 
                           (=> 
                               (exists ((x1563 PZA)) 
                                   (and 
                                       (forall ((x1564 Int) (x1565 A)) 
                                           (= 
                                               (MS1 x1564 x1565 x1563) 
                                               (and 
                                                   (MS1 x1564 x1565 p30) 
                                                   (<= 1 x1564) 
                                                   (<= x1564 i75)))) 
                                       (length x1563 x1562))) 
                               (<= 1 x1562))) 
                       (forall ((x1566 Int)) 
                           (=> 
                               (exists ((x1567 PZA)) 
                                   (and 
                                       (forall ((x1568 Int) (x1569 A)) 
                                           (= 
                                               (MS1 x1568 x1569 x1567) 
                                               (and 
                                                   (MS1 x1568 x1569 p30) 
                                                   (<= 1 x1568) 
                                                   (<= x1568 i75)))) 
                                       (length x1567 x1566))) 
                               (<= x1566 i75))) 
                       (forall ((i77 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i77) 
                                   (forall ((x1570 Int)) 
                                       (=> 
                                           (exists ((x1571 PZA)) 
                                               (and 
                                                   (forall ((x1572 Int) (x1573 A)) 
                                                       (= 
                                                           (MS1 x1572 x1573 x1571) 
                                                           (and 
                                                               (MS1 x1572 x1573 p30) 
                                                               (<= 1 x1572) 
                                                               (<= x1572 i75)))) 
                                                   (length x1571 x1570))) 
                                           (<= i77 (- x1570 1))))) 
                               (exists ((x1574 A) (x1575 A)) 
                                   (and 
                                       (MS1 i77 x1574 p30) 
                                       (<= 1 i77) 
                                       (<= i77 i75) 
                                       (exists ((x1576 Int)) 
                                           (and 
                                               (= x1576 (+ i77 1)) 
                                               (MS1 x1576 x1575 p30))) 
                                       (<= 1 (+ i77 1)) 
                                       (<= (+ i77 1) i75) 
                                       (MS x1574 x1575 r))))))))
         :named hyp105))
(assert (! (forall ((x1577 A) (y40 A) (z4 A)) 
               (=> 
                   (and 
                       (MS0 x1577 a) 
                       (MS0 y40 a) 
                       (MS0 z4 a) 
                       (not 
                           (= z4 x1577)) 
                       (not 
                           (= z4 y40)) 
                       (forall ((t3 A)) 
                           (=> 
                               (and 
                                   (MS0 t3 a) 
                                   (MS z4 t3 r)) 
                               (forall ((x1578 Int) (x1579 Int)) 
                                   (=> 
                                       (and 
                                           (dist x1577 t3 x1579) 
                                           (dist x1577 z4 x1578)) 
                                       (<= x1579 x1578)))))) 
                   (exists ((q2 PZA)) 
                       (and 
                           (exists ((n88 Int)) 
                               (and 
                                   (<= 0 n88) 
                                   (forall ((x1580 Int) (x1581 A)) 
                                       (=> 
                                           (MS1 x1580 x1581 q2) 
                                           (and 
                                               (<= 1 x1580) 
                                               (<= x1580 n88)))) 
                                   (forall ((x1582 Int) (x1583 A) (x1584 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x1582 x1583 q2) 
                                               (MS1 x1582 x1584 q2)) 
                                           (= x1583 x1584))) 
                                   (forall ((x1585 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1585) 
                                               (<= x1585 n88)) 
                                           (exists ((x1586 A)) 
                                               (MS1 x1585 x1586 q2)))))) 
                           (forall ((x1587 A)) 
                               (=> 
                                   (exists ((x1588 Int)) 
                                       (MS1 x1588 x1587 q2)) 
                                   (MS0 x1587 a))) 
                           (forall ((x1589 Int)) 
                               (=> 
                                   (length q2 x1589) 
                                   (< 1 x1589))) 
                           (exists ((x1590 Int)) 
                               (and 
                                   (= x1590 1) 
                                   (MS1 x1590 x1577 q2))) 
                           (exists ((x1591 Int)) 
                               (and 
                                   (length q2 x1591) 
                                   (MS1 x1591 y40 q2))) 
                           (forall ((i78 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i78) 
                                       (forall ((x1592 Int)) 
                                           (=> 
                                               (length q2 x1592) 
                                               (<= i78 (- x1592 1))))) 
                                   (exists ((x1593 A) (x1594 A)) 
                                       (and 
                                           (MS1 i78 x1593 q2) 
                                           (exists ((x1595 Int)) 
                                               (and 
                                                   (= x1595 (+ i78 1)) 
                                                   (MS1 x1595 x1594 q2))) 
                                           (MS x1593 x1594 r))))) 
                           (not 
                               (exists ((x1596 Int)) 
                                   (MS1 x1596 z4 q2)))))))
         :named hyp106))
(assert (! (forall ((x1597 A) (y41 A)) 
               (=> 
                   (and 
                       (MS0 x1597 a) 
                       (MS0 y41 a)) 
                   (exists ((p31 PZA)) 
                       (and 
                           (exists ((n89 Int)) 
                               (and 
                                   (<= 0 n89) 
                                   (forall ((x1598 Int) (x1599 A)) 
                                       (=> 
                                           (MS1 x1598 x1599 p31) 
                                           (and 
                                               (<= 1 x1598) 
                                               (<= x1598 n89)))) 
                                   (forall ((x1600 Int) (x1601 A) (x1602 A)) 
                                       (=> 
                                           (and 
                                               (MS1 x1600 x1601 p31) 
                                               (MS1 x1600 x1602 p31)) 
                                           (= x1601 x1602))) 
                                   (forall ((x1603 Int)) 
                                       (=> 
                                           (and 
                                               (<= 1 x1603) 
                                               (<= x1603 n89)) 
                                           (exists ((x1604 A)) 
                                               (MS1 x1603 x1604 p31)))))) 
                           (forall ((x1605 A)) 
                               (=> 
                                   (exists ((x1606 Int)) 
                                       (MS1 x1606 x1605 p31)) 
                                   (MS0 x1605 a))) 
                           (forall ((x1607 Int)) 
                               (=> 
                                   (length p31 x1607) 
                                   (< 1 x1607))) 
                           (exists ((x1608 Int)) 
                               (and 
                                   (= x1608 1) 
                                   (MS1 x1608 x1597 p31))) 
                           (exists ((x1609 Int)) 
                               (and 
                                   (length p31 x1609) 
                                   (MS1 x1609 y41 p31))) 
                           (forall ((i79 Int)) 
                               (=> 
                                   (and 
                                       (<= 1 i79) 
                                       (forall ((x1610 Int)) 
                                           (=> 
                                               (length p31 x1610) 
                                               (<= i79 (- x1610 1))))) 
                                   (exists ((x1611 A) (x1612 A)) 
                                       (and 
                                           (MS1 i79 x1611 p31) 
                                           (exists ((x1613 Int)) 
                                               (and 
                                                   (= x1613 (+ i79 1)) 
                                                   (MS1 x1613 x1612 p31))) 
                                           (MS x1611 x1612 r))))) 
                           (exists ((x1614 Int)) 
                               (and 
                                   (length p31 x1614) 
                                   (dist x1597 y41 x1614)))))))
         :named hyp107))
(assert (! (exists ((n90 Int)) 
               (and 
                   (<= 0 n90) 
                   (forall ((x1615 Int) (x1616 A)) 
                       (=> 
                           (MS1 x1615 x1616 p) 
                           (and 
                               (<= 1 x1615) 
                               (<= x1615 n90)))) 
                   (forall ((x1617 Int) (x1618 A) (x1619 A)) 
                       (=> 
                           (and 
                               (MS1 x1617 x1618 p) 
                               (MS1 x1617 x1619 p)) 
                           (= x1618 x1619))) 
                   (forall ((x1620 Int)) 
                       (=> 
                           (and 
                               (<= 1 x1620) 
                               (<= x1620 n90)) 
                           (exists ((x1621 A)) 
                               (MS1 x1620 x1621 p))))))
         :named hyp108))
(assert (! (forall ((x1622 A)) 
               (=> 
                   (exists ((x1623 Int)) 
                       (MS1 x1623 x1622 p)) 
                   (MS0 x1622 a)))
         :named hyp109))
(assert (! (forall ((x1624 Int)) 
               (=> 
                   (length p x1624) 
                   (< 1 x1624)))
         :named hyp110))
(assert (! (exists ((x1625 Int)) 
               (and 
                   (= x1625 1) 
                   (MS1 x1625 x p)))
         :named hyp111))
(assert (! (exists ((x1626 Int)) 
               (and 
                   (length p x1626) 
                   (MS1 x1626 y p)))
         :named hyp112))
(assert (! (forall ((i80 Int)) 
               (=> 
                   (and 
                       (<= 1 i80) 
                       (forall ((x1627 Int)) 
                           (=> 
                               (length p x1627) 
                               (<= i80 (- x1627 1))))) 
                   (exists ((x1628 A) (x1629 A)) 
                       (and 
                           (MS1 i80 x1628 p) 
                           (exists ((x1630 Int)) 
                               (and 
                                   (= x1630 (+ i80 1)) 
                                   (MS1 x1630 x1629 p))) 
                           (MS x1628 x1629 r)))))
         :named hyp113))
(assert (! (forall ((x1631 A) (y42 A) (p32 PZA) (i81 Int)) 
               (=> 
                   (and 
                       (MS0 x1631 a) 
                       (MS0 y42 a) 
                       (exists ((n91 Int)) 
                           (and 
                               (<= 0 n91) 
                               (forall ((x1632 Int) (x1633 A)) 
                                   (=> 
                                       (MS1 x1632 x1633 p32) 
                                       (and 
                                           (<= 1 x1632) 
                                           (<= x1632 n91)))) 
                               (forall ((x1634 Int) (x1635 A) (x1636 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1634 x1635 p32) 
                                           (MS1 x1634 x1636 p32)) 
                                       (= x1635 x1636))) 
                               (forall ((x1637 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1637) 
                                           (<= x1637 n91)) 
                                       (exists ((x1638 A)) 
                                           (MS1 x1637 x1638 p32)))))) 
                       (forall ((x1639 A)) 
                           (=> 
                               (exists ((x1640 Int)) 
                                   (MS1 x1640 x1639 p32)) 
                               (MS0 x1639 a))) 
                       (forall ((x1641 Int)) 
                           (=> 
                               (length p32 x1641) 
                               (< 1 x1641))) 
                       (exists ((x1642 Int)) 
                           (and 
                               (= x1642 1) 
                               (MS1 x1642 x1631 p32))) 
                       (exists ((x1643 Int)) 
                           (and 
                               (length p32 x1643) 
                               (MS1 x1643 y42 p32))) 
                       (forall ((i82 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i82) 
                                   (forall ((x1644 Int)) 
                                       (=> 
                                           (length p32 x1644) 
                                           (<= i82 (- x1644 1))))) 
                               (exists ((x1645 A) (x1646 A)) 
                                   (and 
                                       (MS1 i82 x1645 p32) 
                                       (exists ((x1647 Int)) 
                                           (and 
                                               (= x1647 (+ i82 1)) 
                                               (MS1 x1647 x1646 p32))) 
                                       (MS x1645 x1646 r))))) 
                       (exists ((x1648 Int)) 
                           (and 
                               (length p32 x1648) 
                               (dist x1631 y42 x1648))) 
                       (exists ((x1649 A)) 
                           (MS1 i81 x1649 p32)) 
                       (not 
                           (= i81 1)) 
                       (not 
                           (length p32 i81))) 
                   (and 
                       (exists ((n92 Int)) 
                           (and 
                               (<= 0 n92) 
                               (forall ((x1650 Int) (x1651 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1650 x1651 p32) 
                                           (<= 1 x1650) 
                                           (<= x1650 i81)) 
                                       (and 
                                           (<= 1 x1650) 
                                           (<= x1650 n92)))) 
                               (forall ((x1652 Int) (x1653 A) (x1654 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1652 x1653 p32) 
                                           (<= 1 x1652) 
                                           (<= x1652 i81) 
                                           (MS1 x1652 x1654 p32)) 
                                       (= x1653 x1654))) 
                               (forall ((x1655 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1655) 
                                           (<= x1655 n92)) 
                                       (exists ((x1656 A)) 
                                           (and 
                                               (MS1 x1655 x1656 p32) 
                                               (<= 1 x1655) 
                                               (<= x1655 i81))))))) 
                       (forall ((x1657 A)) 
                           (=> 
                               (exists ((x1658 Int)) 
                                   (and 
                                       (MS1 x1658 x1657 p32) 
                                       (<= 1 x1658) 
                                       (<= x1658 i81))) 
                               (MS0 x1657 a))) 
                       (forall ((x1659 Int)) 
                           (=> 
                               (exists ((x1660 PZA)) 
                                   (and 
                                       (forall ((x1661 Int) (x1662 A)) 
                                           (= 
                                               (MS1 x1661 x1662 x1660) 
                                               (and 
                                                   (MS1 x1661 x1662 p32) 
                                                   (<= 1 x1661) 
                                                   (<= x1661 i81)))) 
                                       (length x1660 x1659))) 
                               (< 1 x1659))) 
                       (exists ((x1663 Int)) 
                           (and 
                               (= x1663 1) 
                               (MS1 x1663 x1631 p32))) 
                       (<= 1 1) 
                       (<= 1 i81) 
                       (exists ((x1664 Int) (x1665 A)) 
                           (and 
                               (exists ((x1666 PZA)) 
                                   (and 
                                       (forall ((x1667 Int) (x1668 A)) 
                                           (= 
                                               (MS1 x1667 x1668 x1666) 
                                               (and 
                                                   (MS1 x1667 x1668 p32) 
                                                   (<= 1 x1667) 
                                                   (<= x1667 i81)))) 
                                       (length x1666 x1664))) 
                               (MS1 i81 x1665 p32) 
                               (MS1 x1664 x1665 p32))) 
                       (forall ((x1669 Int)) 
                           (=> 
                               (exists ((x1670 PZA)) 
                                   (and 
                                       (forall ((x1671 Int) (x1672 A)) 
                                           (= 
                                               (MS1 x1671 x1672 x1670) 
                                               (and 
                                                   (MS1 x1671 x1672 p32) 
                                                   (<= 1 x1671) 
                                                   (<= x1671 i81)))) 
                                       (length x1670 x1669))) 
                               (<= 1 x1669))) 
                       (forall ((x1673 Int)) 
                           (=> 
                               (exists ((x1674 PZA)) 
                                   (and 
                                       (forall ((x1675 Int) (x1676 A)) 
                                           (= 
                                               (MS1 x1675 x1676 x1674) 
                                               (and 
                                                   (MS1 x1675 x1676 p32) 
                                                   (<= 1 x1675) 
                                                   (<= x1675 i81)))) 
                                       (length x1674 x1673))) 
                               (<= x1673 i81))) 
                       (forall ((i83 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i83) 
                                   (forall ((x1677 Int)) 
                                       (=> 
                                           (exists ((x1678 PZA)) 
                                               (and 
                                                   (forall ((x1679 Int) (x1680 A)) 
                                                       (= 
                                                           (MS1 x1679 x1680 x1678) 
                                                           (and 
                                                               (MS1 x1679 x1680 p32) 
                                                               (<= 1 x1679) 
                                                               (<= x1679 i81)))) 
                                                   (length x1678 x1677))) 
                                           (<= i83 (- x1677 1))))) 
                               (exists ((x1681 A) (x1682 A)) 
                                   (and 
                                       (MS1 i83 x1681 p32) 
                                       (<= 1 i83) 
                                       (<= i83 i81) 
                                       (exists ((x1683 Int)) 
                                           (and 
                                               (= x1683 (+ i83 1)) 
                                               (MS1 x1683 x1682 p32))) 
                                       (<= 1 (+ i83 1)) 
                                       (<= (+ i83 1) i81) 
                                       (MS x1681 x1682 r))))) 
                       (exists ((x1684 A) (x1685 Int)) 
                           (and 
                               (MS1 i81 x1684 p32) 
                               (exists ((x1686 PZA)) 
                                   (and 
                                       (forall ((x1687 Int) (x1688 A)) 
                                           (= 
                                               (MS1 x1687 x1688 x1686) 
                                               (and 
                                                   (MS1 x1687 x1688 p32) 
                                                   (<= 1 x1687) 
                                                   (<= x1687 i81)))) 
                                       (length x1686 x1685))) 
                               (dist x1631 x1684 x1685))))))
         :named hyp114))
(assert (! (forall ((x1689 A) (y43 A) (p33 PZA) (i84 Int)) 
               (=> 
                   (and 
                       (MS0 x1689 a) 
                       (MS0 y43 a) 
                       (exists ((n93 Int)) 
                           (and 
                               (<= 0 n93) 
                               (forall ((x1690 Int) (x1691 A)) 
                                   (=> 
                                       (MS1 x1690 x1691 p33) 
                                       (and 
                                           (<= 1 x1690) 
                                           (<= x1690 n93)))) 
                               (forall ((x1692 Int) (x1693 A) (x1694 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1692 x1693 p33) 
                                           (MS1 x1692 x1694 p33)) 
                                       (= x1693 x1694))) 
                               (forall ((x1695 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1695) 
                                           (<= x1695 n93)) 
                                       (exists ((x1696 A)) 
                                           (MS1 x1695 x1696 p33)))))) 
                       (forall ((x1697 A)) 
                           (=> 
                               (exists ((x1698 Int)) 
                                   (MS1 x1698 x1697 p33)) 
                               (MS0 x1697 a))) 
                       (forall ((x1699 Int)) 
                           (=> 
                               (length p33 x1699) 
                               (< 1 x1699))) 
                       (exists ((x1700 Int)) 
                           (and 
                               (= x1700 1) 
                               (MS1 x1700 x1689 p33))) 
                       (exists ((x1701 Int)) 
                           (and 
                               (length p33 x1701) 
                               (MS1 x1701 y43 p33))) 
                       (forall ((i85 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i85) 
                                   (forall ((x1702 Int)) 
                                       (=> 
                                           (length p33 x1702) 
                                           (<= i85 (- x1702 1))))) 
                               (exists ((x1703 A) (x1704 A)) 
                                   (and 
                                       (MS1 i85 x1703 p33) 
                                       (exists ((x1705 Int)) 
                                           (and 
                                               (= x1705 (+ i85 1)) 
                                               (MS1 x1705 x1704 p33))) 
                                       (MS x1703 x1704 r))))) 
                       (exists ((x1706 Int)) 
                           (and 
                               (length p33 x1706) 
                               (dist x1689 y43 x1706))) 
                       (exists ((x1707 A)) 
                           (MS1 i84 x1707 p33)) 
                       (not 
                           (= i84 1)) 
                       (not 
                           (length p33 i84))) 
                   (and 
                       (exists ((x1708 A)) 
                           (and 
                               (MS1 i84 x1708 p33) 
                               (dist x1689 x1708 i84))) 
                       (exists ((x1709 A) (x1710 Int)) 
                           (and 
                               (exists ((x1711 Int)) 
                                   (and 
                                       (= x1711 (+ i84 1)) 
                                       (MS1 x1711 x1709 p33))) 
                               (= x1710 (+ i84 1)) 
                               (dist x1689 x1709 x1710))) 
                       (exists ((x1712 A) (x1713 A)) 
                           (and 
                               (MS1 i84 x1712 p33) 
                               (exists ((x1714 Int)) 
                                   (and 
                                       (= x1714 (+ i84 1)) 
                                       (MS1 x1714 x1713 p33))) 
                               (MS x1712 x1713 r))))))
         :named hyp115))
(assert (! (forall ((x1715 A) (y44 A) (p34 PZA) (z5 A)) 
               (=> 
                   (and 
                       (MS0 x1715 a) 
                       (MS0 y44 a) 
                       (exists ((n94 Int)) 
                           (and 
                               (<= 0 n94) 
                               (forall ((x1716 Int) (x1717 A)) 
                                   (=> 
                                       (MS1 x1716 x1717 p34) 
                                       (and 
                                           (<= 1 x1716) 
                                           (<= x1716 n94)))) 
                               (forall ((x1718 Int) (x1719 A) (x1720 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1718 x1719 p34) 
                                           (MS1 x1718 x1720 p34)) 
                                       (= x1719 x1720))) 
                               (forall ((x1721 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1721) 
                                           (<= x1721 n94)) 
                                       (exists ((x1722 A)) 
                                           (MS1 x1721 x1722 p34)))))) 
                       (forall ((x1723 A)) 
                           (=> 
                               (exists ((x1724 Int)) 
                                   (MS1 x1724 x1723 p34)) 
                               (MS0 x1723 a))) 
                       (forall ((x1725 Int)) 
                           (=> 
                               (length p34 x1725) 
                               (< 1 x1725))) 
                       (exists ((x1726 Int)) 
                           (and 
                               (= x1726 1) 
                               (MS1 x1726 x1715 p34))) 
                       (exists ((x1727 Int)) 
                           (and 
                               (length p34 x1727) 
                               (MS1 x1727 y44 p34))) 
                       (forall ((i86 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i86) 
                                   (forall ((x1728 Int)) 
                                       (=> 
                                           (length p34 x1728) 
                                           (<= i86 (- x1728 1))))) 
                               (exists ((x1729 A) (x1730 A)) 
                                   (and 
                                       (MS1 i86 x1729 p34) 
                                       (exists ((x1731 Int)) 
                                           (and 
                                               (= x1731 (+ i86 1)) 
                                               (MS1 x1731 x1730 p34))) 
                                       (MS x1729 x1730 r))))) 
                       (exists ((x1732 Int)) 
                           (and 
                               (length p34 x1732) 
                               (dist x1715 y44 x1732))) 
                       (exists ((x1733 Int)) 
                           (MS1 x1733 z5 p34)) 
                       (not 
                           (= z5 x1715)) 
                       (not 
                           (= z5 y44))) 
                   (exists ((t4 A)) 
                       (and 
                           (MS0 t4 a) 
                           (forall ((x1734 Int) (x1735 Int)) 
                               (=> 
                                   (and 
                                       (dist x1715 z5 x1735) 
                                       (dist x1715 t4 x1734)) 
                                   (< x1735 x1734))) 
                           (MS z5 t4 r)))))
         :named hyp116))
(assert (! (forall ((y111 A) (y211 A) (x1736 A) (x1737 A) (p35 PZA) (q3 PZA)) 
               (=> 
                   (and 
                       (MS0 y111 a) 
                       (MS0 y211 a) 
                       (MS0 x1736 a) 
                       (MS0 x1737 a) 
                       (exists ((n95 Int)) 
                           (and 
                               (<= 0 n95) 
                               (forall ((x1738 Int) (x1739 A)) 
                                   (=> 
                                       (MS1 x1738 x1739 q3) 
                                       (and 
                                           (<= 1 x1738) 
                                           (<= x1738 n95)))) 
                               (forall ((x1740 Int) (x1741 A) (x1742 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1740 x1741 q3) 
                                           (MS1 x1740 x1742 q3)) 
                                       (= x1741 x1742))) 
                               (forall ((x1743 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1743) 
                                           (<= x1743 n95)) 
                                       (exists ((x1744 A)) 
                                           (MS1 x1743 x1744 q3)))))) 
                       (forall ((x1745 A)) 
                           (=> 
                               (exists ((x1746 Int)) 
                                   (MS1 x1746 x1745 q3)) 
                               (MS0 x1745 a))) 
                       (forall ((x1747 Int)) 
                           (=> 
                               (length q3 x1747) 
                               (< 1 x1747))) 
                       (exists ((x1748 Int)) 
                           (and 
                               (= x1748 1) 
                               (MS1 x1748 x1736 q3))) 
                       (exists ((x1749 Int)) 
                           (and 
                               (length q3 x1749) 
                               (MS1 x1749 y111 q3))) 
                       (forall ((i87 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i87) 
                                   (forall ((x1750 Int)) 
                                       (=> 
                                           (length q3 x1750) 
                                           (<= i87 (- x1750 1))))) 
                               (exists ((x1751 A) (x1752 A)) 
                                   (and 
                                       (MS1 i87 x1751 q3) 
                                       (exists ((x1753 Int)) 
                                           (and 
                                               (= x1753 (+ i87 1)) 
                                               (MS1 x1753 x1752 q3))) 
                                       (MS x1751 x1752 r))))) 
                       (exists ((n96 Int)) 
                           (and 
                               (<= 0 n96) 
                               (forall ((x1754 Int) (x1755 A)) 
                                   (=> 
                                       (MS1 x1754 x1755 p35) 
                                       (and 
                                           (<= 1 x1754) 
                                           (<= x1754 n96)))) 
                               (forall ((x1756 Int) (x1757 A) (x1758 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1756 x1757 p35) 
                                           (MS1 x1756 x1758 p35)) 
                                       (= x1757 x1758))) 
                               (forall ((x1759 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1759) 
                                           (<= x1759 n96)) 
                                       (exists ((x1760 A)) 
                                           (MS1 x1759 x1760 p35)))))) 
                       (forall ((x1761 A)) 
                           (=> 
                               (exists ((x1762 Int)) 
                                   (MS1 x1762 x1761 p35)) 
                               (MS0 x1761 a))) 
                       (forall ((x1763 Int)) 
                           (=> 
                               (length p35 x1763) 
                               (< 1 x1763))) 
                       (exists ((x1764 Int)) 
                           (and 
                               (= x1764 1) 
                               (MS1 x1764 y211 p35))) 
                       (exists ((x1765 Int)) 
                           (and 
                               (length p35 x1765) 
                               (MS1 x1765 x1737 p35))) 
                       (forall ((i88 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i88) 
                                   (forall ((x1766 Int)) 
                                       (=> 
                                           (length p35 x1766) 
                                           (<= i88 (- x1766 1))))) 
                               (exists ((x1767 A) (x1768 A)) 
                                   (and 
                                       (MS1 i88 x1767 p35) 
                                       (exists ((x1769 Int)) 
                                           (and 
                                               (= x1769 (+ i88 1)) 
                                               (MS1 x1769 x1768 p35))) 
                                       (MS x1767 x1768 r))))) 
                       (MS x1737 x1736 r)) 
                   (and 
                       (exists ((n97 Int)) 
                           (and 
                               (<= 0 n97) 
                               (forall ((x1770 Int) (x1771 A)) 
                                   (=> 
                                       (or 
                                           (exists ((i89 Int)) 
                                               (and 
                                                   (<= 1 i89) 
                                                   (forall ((x1772 Int)) 
                                                       (=> 
                                                           (length p35 x1772) 
                                                           (<= i89 x1772))) 
                                                   (= x1770 i89) 
                                                   (MS1 i89 x1771 p35))) 
                                           (exists ((i90 Int)) 
                                               (and 
                                                   (forall ((x1773 Int)) 
                                                       (=> 
                                                           (length p35 x1773) 
                                                           (<= (+ x1773 1) i90))) 
                                                   (forall ((x1774 Int) (x1775 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p35 x1775) 
                                                               (length q3 x1774)) 
                                                           (<= i90 (+ x1775 x1774)))) 
                                                   (= x1770 i90) 
                                                   (exists ((x1776 Int)) 
                                                       (and 
                                                           (forall ((x1777 Int)) 
                                                               (=> 
                                                                   (length p35 x1777) 
                                                                   (= x1776 (- i90 x1777)))) 
                                                           (MS1 x1776 x1771 q3)))))) 
                                       (and 
                                           (<= 1 x1770) 
                                           (<= x1770 n97)))) 
                               (forall ((x1778 Int) (x1779 A) (x1780 A)) 
                                   (=> 
                                       (and 
                                           (or 
                                               (exists ((i91 Int)) 
                                                   (and 
                                                       (<= 1 i91) 
                                                       (forall ((x1781 Int)) 
                                                           (=> 
                                                               (length p35 x1781) 
                                                               (<= i91 x1781))) 
                                                       (= x1778 i91) 
                                                       (MS1 i91 x1779 p35))) 
                                               (exists ((i92 Int)) 
                                                   (and 
                                                       (forall ((x1782 Int)) 
                                                           (=> 
                                                               (length p35 x1782) 
                                                               (<= (+ x1782 1) i92))) 
                                                       (forall ((x1783 Int) (x1784 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p35 x1784) 
                                                                   (length q3 x1783)) 
                                                               (<= i92 (+ x1784 x1783)))) 
                                                       (= x1778 i92) 
                                                       (exists ((x1785 Int)) 
                                                           (and 
                                                               (forall ((x1786 Int)) 
                                                                   (=> 
                                                                       (length p35 x1786) 
                                                                       (= x1785 (- i92 x1786)))) 
                                                               (MS1 x1785 x1779 q3)))))) 
                                           (or 
                                               (exists ((i93 Int)) 
                                                   (and 
                                                       (<= 1 i93) 
                                                       (forall ((x1787 Int)) 
                                                           (=> 
                                                               (length p35 x1787) 
                                                               (<= i93 x1787))) 
                                                       (= x1778 i93) 
                                                       (MS1 i93 x1780 p35))) 
                                               (exists ((i94 Int)) 
                                                   (and 
                                                       (forall ((x1788 Int)) 
                                                           (=> 
                                                               (length p35 x1788) 
                                                               (<= (+ x1788 1) i94))) 
                                                       (forall ((x1789 Int) (x1790 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p35 x1790) 
                                                                   (length q3 x1789)) 
                                                               (<= i94 (+ x1790 x1789)))) 
                                                       (= x1778 i94) 
                                                       (exists ((x1791 Int)) 
                                                           (and 
                                                               (forall ((x1792 Int)) 
                                                                   (=> 
                                                                       (length p35 x1792) 
                                                                       (= x1791 (- i94 x1792)))) 
                                                               (MS1 x1791 x1780 q3))))))) 
                                       (= x1779 x1780))) 
                               (forall ((x1793 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1793) 
                                           (<= x1793 n97)) 
                                       (or 
                                           (exists ((x1794 A)) 
                                               (exists ((i95 Int)) 
                                                   (and 
                                                       (<= 1 i95) 
                                                       (forall ((x1795 Int)) 
                                                           (=> 
                                                               (length p35 x1795) 
                                                               (<= i95 x1795))) 
                                                       (= x1793 i95) 
                                                       (MS1 i95 x1794 p35)))) 
                                           (exists ((x1796 A)) 
                                               (exists ((i96 Int)) 
                                                   (and 
                                                       (forall ((x1797 Int)) 
                                                           (=> 
                                                               (length p35 x1797) 
                                                               (<= (+ x1797 1) i96))) 
                                                       (forall ((x1798 Int) (x1799 Int)) 
                                                           (=> 
                                                               (and 
                                                                   (length p35 x1799) 
                                                                   (length q3 x1798)) 
                                                               (<= i96 (+ x1799 x1798)))) 
                                                       (= x1793 i96) 
                                                       (exists ((x1800 Int)) 
                                                           (and 
                                                               (forall ((x1801 Int)) 
                                                                   (=> 
                                                                       (length p35 x1801) 
                                                                       (= x1800 (- i96 x1801)))) 
                                                               (MS1 x1800 x1796 q3))))))))))) 
                       (forall ((x1802 A)) 
                           (=> 
                               (or 
                                   (exists ((x1803 Int)) 
                                       (exists ((i97 Int)) 
                                           (and 
                                               (<= 1 i97) 
                                               (forall ((x1804 Int)) 
                                                   (=> 
                                                       (length p35 x1804) 
                                                       (<= i97 x1804))) 
                                               (= x1803 i97) 
                                               (MS1 i97 x1802 p35)))) 
                                   (exists ((x1805 Int)) 
                                       (exists ((i98 Int)) 
                                           (and 
                                               (forall ((x1806 Int)) 
                                                   (=> 
                                                       (length p35 x1806) 
                                                       (<= (+ x1806 1) i98))) 
                                               (forall ((x1807 Int) (x1808 Int)) 
                                                   (=> 
                                                       (and 
                                                           (length p35 x1808) 
                                                           (length q3 x1807)) 
                                                       (<= i98 (+ x1808 x1807)))) 
                                               (= x1805 i98) 
                                               (exists ((x1809 Int)) 
                                                   (and 
                                                       (forall ((x1810 Int)) 
                                                           (=> 
                                                               (length p35 x1810) 
                                                               (= x1809 (- i98 x1810)))) 
                                                       (MS1 x1809 x1802 q3))))))) 
                               (MS0 x1802 a))) 
                       (forall ((x1811 Int)) 
                           (=> 
                               (exists ((x1812 PZA)) 
                                   (and 
                                       (forall ((x1813 Int) (x1814 A)) 
                                           (= 
                                               (MS1 x1813 x1814 x1812) 
                                               (or 
                                                   (exists ((i99 Int)) 
                                                       (and 
                                                           (<= 1 i99) 
                                                           (forall ((x1815 Int)) 
                                                               (=> 
                                                                   (length p35 x1815) 
                                                                   (<= i99 x1815))) 
                                                           (= x1813 i99) 
                                                           (MS1 i99 x1814 p35))) 
                                                   (exists ((i100 Int)) 
                                                       (and 
                                                           (forall ((x1816 Int)) 
                                                               (=> 
                                                                   (length p35 x1816) 
                                                                   (<= (+ x1816 1) i100))) 
                                                           (forall ((x1817 Int) (x1818 Int)) 
                                                               (=> 
                                                                   (and 
                                                                       (length p35 x1818) 
                                                                       (length q3 x1817)) 
                                                                   (<= i100 (+ x1818 x1817)))) 
                                                           (= x1813 i100) 
                                                           (exists ((x1819 Int)) 
                                                               (and 
                                                                   (forall ((x1820 Int)) 
                                                                       (=> 
                                                                           (length p35 x1820) 
                                                                           (= x1819 (- i100 x1820)))) 
                                                                   (MS1 x1819 x1814 q3)))))))) 
                                       (length x1812 x1811))) 
                               (< 1 x1811))) 
                       (or 
                           (exists ((i101 Int)) 
                               (and 
                                   (<= 1 i101) 
                                   (forall ((x1821 Int)) 
                                       (=> 
                                           (length p35 x1821) 
                                           (<= i101 x1821))) 
                                   (= 1 i101) 
                                   (MS1 i101 y211 p35))) 
                           (exists ((i102 Int)) 
                               (and 
                                   (forall ((x1822 Int)) 
                                       (=> 
                                           (length p35 x1822) 
                                           (<= (+ x1822 1) i102))) 
                                   (forall ((x1823 Int) (x1824 Int)) 
                                       (=> 
                                           (and 
                                               (length p35 x1824) 
                                               (length q3 x1823)) 
                                           (<= i102 (+ x1824 x1823)))) 
                                   (= 1 i102) 
                                   (exists ((x1825 Int)) 
                                       (and 
                                           (forall ((x1826 Int)) 
                                               (=> 
                                                   (length p35 x1826) 
                                                   (= x1825 (- i102 x1826)))) 
                                           (MS1 x1825 y211 q3)))))) 
                       (or 
                           (exists ((i103 Int)) 
                               (and 
                                   (<= 1 i103) 
                                   (forall ((x1827 Int)) 
                                       (=> 
                                           (length p35 x1827) 
                                           (<= i103 x1827))) 
                                   (exists ((x1828 PZA)) 
                                       (and 
                                           (forall ((x1829 Int) (x1830 A)) 
                                               (= 
                                                   (MS1 x1829 x1830 x1828) 
                                                   (or 
                                                       (exists ((i104 Int)) 
                                                           (and 
                                                               (<= 1 i104) 
                                                               (forall ((x1831 Int)) 
                                                                   (=> 
                                                                       (length p35 x1831) 
                                                                       (<= i104 x1831))) 
                                                               (= x1829 i104) 
                                                               (MS1 i104 x1830 p35))) 
                                                       (exists ((i105 Int)) 
                                                           (and 
                                                               (forall ((x1832 Int)) 
                                                                   (=> 
                                                                       (length p35 x1832) 
                                                                       (<= (+ x1832 1) i105))) 
                                                               (forall ((x1833 Int) (x1834 Int)) 
                                                                   (=> 
                                                                       (and 
                                                                           (length p35 x1834) 
                                                                           (length q3 x1833)) 
                                                                       (<= i105 (+ x1834 x1833)))) 
                                                               (= x1829 i105) 
                                                               (exists ((x1835 Int)) 
                                                                   (and 
                                                                       (forall ((x1836 Int)) 
                                                                           (=> 
                                                                               (length p35 x1836) 
                                                                               (= x1835 (- i105 x1836)))) 
                                                                       (MS1 x1835 x1830 q3)))))))) 
                                           (length x1828 i103))) 
                                   (MS1 i103 y111 p35))) 
                           (exists ((i106 Int)) 
                               (and 
                                   (forall ((x1837 Int)) 
                                       (=> 
                                           (length p35 x1837) 
                                           (<= (+ x1837 1) i106))) 
                                   (forall ((x1838 Int) (x1839 Int)) 
                                       (=> 
                                           (and 
                                               (length p35 x1839) 
                                               (length q3 x1838)) 
                                           (<= i106 (+ x1839 x1838)))) 
                                   (exists ((x1840 PZA)) 
                                       (and 
                                           (forall ((x1841 Int) (x1842 A)) 
                                               (= 
                                                   (MS1 x1841 x1842 x1840) 
                                                   (or 
                                                       (exists ((i107 Int)) 
                                                           (and 
                                                               (<= 1 i107) 
                                                               (forall ((x1843 Int)) 
                                                                   (=> 
                                                                       (length p35 x1843) 
                                                                       (<= i107 x1843))) 
                                                               (= x1841 i107) 
                                                               (MS1 i107 x1842 p35))) 
                                                       (exists ((i108 Int)) 
                                                           (and 
                                                               (forall ((x1844 Int)) 
                                                                   (=> 
                                                                       (length p35 x1844) 
                                                                       (<= (+ x1844 1) i108))) 
                                                               (forall ((x1845 Int) (x1846 Int)) 
                                                                   (=> 
                                                                       (and 
                                                                           (length p35 x1846) 
                                                                           (length q3 x1845)) 
                                                                       (<= i108 (+ x1846 x1845)))) 
                                                               (= x1841 i108) 
                                                               (exists ((x1847 Int)) 
                                                                   (and 
                                                                       (forall ((x1848 Int)) 
                                                                           (=> 
                                                                               (length p35 x1848) 
                                                                               (= x1847 (- i108 x1848)))) 
                                                                       (MS1 x1847 x1842 q3)))))))) 
                                           (length x1840 i106))) 
                                   (exists ((x1849 Int)) 
                                       (and 
                                           (forall ((x1850 Int)) 
                                               (=> 
                                                   (length p35 x1850) 
                                                   (= x1849 (- i106 x1850)))) 
                                           (MS1 x1849 y111 q3)))))) 
                       (forall ((i109 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i109) 
                                   (forall ((x1851 Int)) 
                                       (=> 
                                           (exists ((x1852 PZA)) 
                                               (and 
                                                   (forall ((x1853 Int) (x1854 A)) 
                                                       (= 
                                                           (MS1 x1853 x1854 x1852) 
                                                           (or 
                                                               (exists ((i110 Int)) 
                                                                   (and 
                                                                       (<= 1 i110) 
                                                                       (forall ((x1855 Int)) 
                                                                           (=> 
                                                                               (length p35 x1855) 
                                                                               (<= i110 x1855))) 
                                                                       (= x1853 i110) 
                                                                       (MS1 i110 x1854 p35))) 
                                                               (exists ((i111 Int)) 
                                                                   (and 
                                                                       (forall ((x1856 Int)) 
                                                                           (=> 
                                                                               (length p35 x1856) 
                                                                               (<= (+ x1856 1) i111))) 
                                                                       (forall ((x1857 Int) (x1858 Int)) 
                                                                           (=> 
                                                                               (and 
                                                                                   (length p35 x1858) 
                                                                                   (length q3 x1857)) 
                                                                               (<= i111 (+ x1858 x1857)))) 
                                                                       (= x1853 i111) 
                                                                       (exists ((x1859 Int)) 
                                                                           (and 
                                                                               (forall ((x1860 Int)) 
                                                                                   (=> 
                                                                                       (length p35 x1860) 
                                                                                       (= x1859 (- i111 x1860)))) 
                                                                               (MS1 x1859 x1854 q3)))))))) 
                                                   (length x1852 x1851))) 
                                           (<= i109 (- x1851 1))))) 
                               (exists ((x1861 A) (x1862 A)) 
                                   (and 
                                       (or 
                                           (exists ((i112 Int)) 
                                               (and 
                                                   (<= 1 i112) 
                                                   (forall ((x1863 Int)) 
                                                       (=> 
                                                           (length p35 x1863) 
                                                           (<= i112 x1863))) 
                                                   (= i109 i112) 
                                                   (MS1 i112 x1861 p35))) 
                                           (exists ((i113 Int)) 
                                               (and 
                                                   (forall ((x1864 Int)) 
                                                       (=> 
                                                           (length p35 x1864) 
                                                           (<= (+ x1864 1) i113))) 
                                                   (forall ((x1865 Int) (x1866 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p35 x1866) 
                                                               (length q3 x1865)) 
                                                           (<= i113 (+ x1866 x1865)))) 
                                                   (= i109 i113) 
                                                   (exists ((x1867 Int)) 
                                                       (and 
                                                           (forall ((x1868 Int)) 
                                                               (=> 
                                                                   (length p35 x1868) 
                                                                   (= x1867 (- i113 x1868)))) 
                                                           (MS1 x1867 x1861 q3)))))) 
                                       (or 
                                           (exists ((i114 Int)) 
                                               (and 
                                                   (<= 1 i114) 
                                                   (forall ((x1869 Int)) 
                                                       (=> 
                                                           (length p35 x1869) 
                                                           (<= i114 x1869))) 
                                                   (= (+ i109 1) i114) 
                                                   (MS1 i114 x1862 p35))) 
                                           (exists ((i115 Int)) 
                                               (and 
                                                   (forall ((x1870 Int)) 
                                                       (=> 
                                                           (length p35 x1870) 
                                                           (<= (+ x1870 1) i115))) 
                                                   (forall ((x1871 Int) (x1872 Int)) 
                                                       (=> 
                                                           (and 
                                                               (length p35 x1872) 
                                                               (length q3 x1871)) 
                                                           (<= i115 (+ x1872 x1871)))) 
                                                   (= (+ i109 1) i115) 
                                                   (exists ((x1873 Int)) 
                                                       (and 
                                                           (forall ((x1874 Int)) 
                                                               (=> 
                                                                   (length p35 x1874) 
                                                                   (= x1873 (- i115 x1874)))) 
                                                           (MS1 x1873 x1862 q3)))))) 
                                       (MS x1861 x1862 r))))))))
         :named hyp117))
(assert (! (forall ((x1875 A) (y45 A) (p36 PZA)) 
               (=> 
                   (and 
                       (exists ((n98 Int)) 
                           (and 
                               (<= 0 n98) 
                               (forall ((x1876 Int) (x1877 A)) 
                                   (=> 
                                       (MS1 x1876 x1877 p36) 
                                       (and 
                                           (<= 1 x1876) 
                                           (<= x1876 n98)))) 
                               (forall ((x1878 Int) (x1879 A) (x1880 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1878 x1879 p36) 
                                           (MS1 x1878 x1880 p36)) 
                                       (= x1879 x1880))) 
                               (forall ((x1881 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1881) 
                                           (<= x1881 n98)) 
                                       (exists ((x1882 A)) 
                                           (MS1 x1881 x1882 p36)))))) 
                       (forall ((x1883 A)) 
                           (=> 
                               (exists ((x1884 Int)) 
                                   (MS1 x1884 x1883 p36)) 
                               (MS0 x1883 a))) 
                       (forall ((x1885 Int)) 
                           (=> 
                               (length p36 x1885) 
                               (< 1 x1885))) 
                       (exists ((x1886 Int)) 
                           (and 
                               (= x1886 1) 
                               (MS1 x1886 x1875 p36))) 
                       (exists ((x1887 Int)) 
                           (and 
                               (length p36 x1887) 
                               (MS1 x1887 y45 p36))) 
                       (forall ((i116 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i116) 
                                   (forall ((x1888 Int)) 
                                       (=> 
                                           (length p36 x1888) 
                                           (<= i116 (- x1888 1))))) 
                               (exists ((x1889 A) (x1890 A)) 
                                   (and 
                                       (MS1 i116 x1889 p36) 
                                       (exists ((x1891 Int)) 
                                           (and 
                                               (= x1891 (+ i116 1)) 
                                               (MS1 x1891 x1890 p36))) 
                                       (MS x1889 x1890 r)))))) 
                   (and 
                       (exists ((n99 Int)) 
                           (and 
                               (<= 0 n99) 
                               (forall ((x1892 Int) (x1893 A)) 
                                   (=> 
                                       (exists ((i117 Int)) 
                                           (and 
                                               (<= 1 i117) 
                                               (forall ((x1894 Int)) 
                                                   (=> 
                                                       (length p36 x1894) 
                                                       (<= i117 x1894))) 
                                               (= x1892 i117) 
                                               (exists ((x1895 Int)) 
                                                   (and 
                                                       (forall ((x1896 Int)) 
                                                           (=> 
                                                               (length p36 x1896) 
                                                               (= x1895 (+ (- x1896 i117) 1)))) 
                                                       (MS1 x1895 x1893 p36))))) 
                                       (and 
                                           (<= 1 x1892) 
                                           (<= x1892 n99)))) 
                               (forall ((x1897 Int) (x1898 A) (x1899 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i118 Int)) 
                                               (and 
                                                   (<= 1 i118) 
                                                   (forall ((x1900 Int)) 
                                                       (=> 
                                                           (length p36 x1900) 
                                                           (<= i118 x1900))) 
                                                   (= x1897 i118) 
                                                   (exists ((x1901 Int)) 
                                                       (and 
                                                           (forall ((x1902 Int)) 
                                                               (=> 
                                                                   (length p36 x1902) 
                                                                   (= x1901 (+ (- x1902 i118) 1)))) 
                                                           (MS1 x1901 x1898 p36))))) 
                                           (exists ((i119 Int)) 
                                               (and 
                                                   (<= 1 i119) 
                                                   (forall ((x1903 Int)) 
                                                       (=> 
                                                           (length p36 x1903) 
                                                           (<= i119 x1903))) 
                                                   (= x1897 i119) 
                                                   (exists ((x1904 Int)) 
                                                       (and 
                                                           (forall ((x1905 Int)) 
                                                               (=> 
                                                                   (length p36 x1905) 
                                                                   (= x1904 (+ (- x1905 i119) 1)))) 
                                                           (MS1 x1904 x1899 p36)))))) 
                                       (= x1898 x1899))) 
                               (forall ((x1906 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1906) 
                                           (<= x1906 n99)) 
                                       (exists ((x1907 A) (i120 Int)) 
                                           (and 
                                               (<= 1 i120) 
                                               (forall ((x1908 Int)) 
                                                   (=> 
                                                       (length p36 x1908) 
                                                       (<= i120 x1908))) 
                                               (= x1906 i120) 
                                               (exists ((x1909 Int)) 
                                                   (and 
                                                       (forall ((x1910 Int)) 
                                                           (=> 
                                                               (length p36 x1910) 
                                                               (= x1909 (+ (- x1910 i120) 1)))) 
                                                       (MS1 x1909 x1907 p36))))))))) 
                       (forall ((i121 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i121) 
                                   (forall ((x1911 Int)) 
                                       (=> 
                                           (length p36 x1911) 
                                           (<= i121 x1911)))) 
                               (exists ((x1912 A)) 
                                   (and 
                                       (exists ((x1913 Int)) 
                                           (and 
                                               (forall ((x1914 Int)) 
                                                   (=> 
                                                       (length p36 x1914) 
                                                       (= x1913 (+ (- x1914 i121) 1)))) 
                                               (MS1 x1913 x1912 p36))) 
                                       (MS0 x1912 a))))) 
                       (forall ((x1915 Int)) 
                           (=> 
                               (exists ((x1916 PZA)) 
                                   (and 
                                       (forall ((x1917 Int) (x1918 A)) 
                                           (= 
                                               (MS1 x1917 x1918 x1916) 
                                               (exists ((i122 Int)) 
                                                   (and 
                                                       (<= 1 i122) 
                                                       (forall ((x1919 Int)) 
                                                           (=> 
                                                               (length p36 x1919) 
                                                               (<= i122 x1919))) 
                                                       (= x1917 i122) 
                                                       (exists ((x1920 Int)) 
                                                           (and 
                                                               (forall ((x1921 Int)) 
                                                                   (=> 
                                                                       (length p36 x1921) 
                                                                       (= x1920 (+ (- x1921 i122) 1)))) 
                                                               (MS1 x1920 x1918 p36))))))) 
                                       (length x1916 x1915))) 
                               (< 1 x1915))) 
                       (exists ((x1922 Int)) 
                           (and 
                               (forall ((x1923 Int)) 
                                   (=> 
                                       (length p36 x1923) 
                                       (= x1922 (+ (- x1923 1) 1)))) 
                               (MS1 x1922 y45 p36))) 
                       (exists ((x1924 Int)) 
                           (and 
                               (forall ((x1925 Int) (x1926 Int)) 
                                   (=> 
                                       (and 
                                           (length p36 x1926) 
                                           (exists ((x1927 PZA)) 
                                               (and 
                                                   (forall ((x1928 Int) (x1929 A)) 
                                                       (= 
                                                           (MS1 x1928 x1929 x1927) 
                                                           (exists ((i123 Int)) 
                                                               (and 
                                                                   (<= 1 i123) 
                                                                   (forall ((x1930 Int)) 
                                                                       (=> 
                                                                           (length p36 x1930) 
                                                                           (<= i123 x1930))) 
                                                                   (= x1928 i123) 
                                                                   (exists ((x1931 Int)) 
                                                                       (and 
                                                                           (forall ((x1932 Int)) 
                                                                               (=> 
                                                                                   (length p36 x1932) 
                                                                                   (= x1931 (+ (- x1932 i123) 1)))) 
                                                                           (MS1 x1931 x1929 p36))))))) 
                                                   (length x1927 x1925)))) 
                                       (= x1924 (+ (- x1926 x1925) 1)))) 
                               (MS1 x1924 x1875 p36))) 
                       (forall ((i124 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i124) 
                                   (forall ((x1933 Int)) 
                                       (=> 
                                           (exists ((x1934 PZA)) 
                                               (and 
                                                   (forall ((x1935 Int) (x1936 A)) 
                                                       (= 
                                                           (MS1 x1935 x1936 x1934) 
                                                           (exists ((i125 Int)) 
                                                               (and 
                                                                   (<= 1 i125) 
                                                                   (forall ((x1937 Int)) 
                                                                       (=> 
                                                                           (length p36 x1937) 
                                                                           (<= i125 x1937))) 
                                                                   (= x1935 i125) 
                                                                   (exists ((x1938 Int)) 
                                                                       (and 
                                                                           (forall ((x1939 Int)) 
                                                                               (=> 
                                                                                   (length p36 x1939) 
                                                                                   (= x1938 (+ (- x1939 i125) 1)))) 
                                                                           (MS1 x1938 x1936 p36))))))) 
                                                   (length x1934 x1933))) 
                                           (<= i124 (- x1933 1))))) 
                               (exists ((x1940 A) (x1941 A)) 
                                   (and 
                                       (exists ((x1942 Int)) 
                                           (and 
                                               (forall ((x1943 Int)) 
                                                   (=> 
                                                       (length p36 x1943) 
                                                       (= x1942 (+ (- x1943 i124) 1)))) 
                                               (MS1 x1942 x1940 p36))) 
                                       (exists ((x1944 Int)) 
                                           (and 
                                               (forall ((x1945 Int)) 
                                                   (=> 
                                                       (length p36 x1945) 
                                                       (= x1944 (+ (- x1945 (+ i124 1)) 1)))) 
                                               (MS1 x1944 x1941 p36))) 
                                       (MS x1940 x1941 r))))))))
         :named hyp118))
(assert (! (forall ((x1946 A) (y212 A) (p37 PZA)) 
               (=> 
                   (and 
                       (MS0 x1946 a) 
                       (MS0 y212 a) 
                       (exists ((n100 Int)) 
                           (and 
                               (<= 0 n100) 
                               (forall ((x1947 Int) (x1948 A)) 
                                   (=> 
                                       (MS1 x1947 x1948 p37) 
                                       (and 
                                           (<= 1 x1947) 
                                           (<= x1947 n100)))) 
                               (forall ((x1949 Int) (x1950 A) (x1951 A)) 
                                   (=> 
                                       (and 
                                           (MS1 x1949 x1950 p37) 
                                           (MS1 x1949 x1951 p37)) 
                                       (= x1950 x1951))) 
                               (forall ((x1952 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1952) 
                                           (<= x1952 n100)) 
                                       (exists ((x1953 A)) 
                                           (MS1 x1952 x1953 p37)))))) 
                       (forall ((x1954 A)) 
                           (=> 
                               (exists ((x1955 Int)) 
                                   (MS1 x1955 x1954 p37)) 
                               (MS0 x1954 a))) 
                       (forall ((x1956 Int)) 
                           (=> 
                               (length p37 x1956) 
                               (< 1 x1956))) 
                       (exists ((x1957 Int)) 
                           (and 
                               (= x1957 1) 
                               (MS1 x1957 x1946 p37))) 
                       (exists ((x1958 Int)) 
                           (and 
                               (length p37 x1958) 
                               (MS1 x1958 y212 p37))) 
                       (forall ((i126 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i126) 
                                   (forall ((x1959 Int)) 
                                       (=> 
                                           (length p37 x1959) 
                                           (<= i126 (- x1959 1))))) 
                               (exists ((x1960 A) (x1961 A)) 
                                   (and 
                                       (MS1 i126 x1960 p37) 
                                       (exists ((x1962 Int)) 
                                           (and 
                                               (= x1962 (+ i126 1)) 
                                               (MS1 x1962 x1961 p37))) 
                                       (MS x1960 x1961 r))))) 
                       (forall ((x1963 Int)) 
                           (=> 
                               (length p37 x1963) 
                               (<= 3 x1963)))) 
                   (and 
                       (exists ((n101 Int)) 
                           (and 
                               (<= 0 n101) 
                               (forall ((x1964 Int) (x1965 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i127 Int)) 
                                               (and 
                                                   (<= 1 i127) 
                                                   (forall ((x1966 Int)) 
                                                       (=> 
                                                           (length p37 x1966) 
                                                           (<= i127 x1966))) 
                                                   (= x1964 i127) 
                                                   (exists ((x1967 Int)) 
                                                       (and 
                                                           (forall ((x1968 Int)) 
                                                               (=> 
                                                                   (length p37 x1968) 
                                                                   (= x1967 (+ (- x1968 i127) 1)))) 
                                                           (MS1 x1967 x1965 p37))))) 
                                           (<= 1 x1964) 
                                           (forall ((x1969 Int)) 
                                               (=> 
                                                   (length p37 x1969) 
                                                   (<= x1964 (- x1969 1))))) 
                                       (and 
                                           (<= 1 x1964) 
                                           (<= x1964 n101)))) 
                               (forall ((x1970 Int) (x1971 A) (x1972 A)) 
                                   (=> 
                                       (and 
                                           (exists ((i128 Int)) 
                                               (and 
                                                   (<= 1 i128) 
                                                   (forall ((x1973 Int)) 
                                                       (=> 
                                                           (length p37 x1973) 
                                                           (<= i128 x1973))) 
                                                   (= x1970 i128) 
                                                   (exists ((x1974 Int)) 
                                                       (and 
                                                           (forall ((x1975 Int)) 
                                                               (=> 
                                                                   (length p37 x1975) 
                                                                   (= x1974 (+ (- x1975 i128) 1)))) 
                                                           (MS1 x1974 x1971 p37))))) 
                                           (<= 1 x1970) 
                                           (forall ((x1976 Int)) 
                                               (=> 
                                                   (length p37 x1976) 
                                                   (<= x1970 (- x1976 1)))) 
                                           (exists ((i129 Int)) 
                                               (and 
                                                   (<= 1 i129) 
                                                   (forall ((x1977 Int)) 
                                                       (=> 
                                                           (length p37 x1977) 
                                                           (<= i129 x1977))) 
                                                   (= x1970 i129) 
                                                   (exists ((x1978 Int)) 
                                                       (and 
                                                           (forall ((x1979 Int)) 
                                                               (=> 
                                                                   (length p37 x1979) 
                                                                   (= x1978 (+ (- x1979 i129) 1)))) 
                                                           (MS1 x1978 x1972 p37)))))) 
                                       (= x1971 x1972))) 
                               (forall ((x1980 Int)) 
                                   (=> 
                                       (and 
                                           (<= 1 x1980) 
                                           (<= x1980 n101)) 
                                       (exists ((x1981 A)) 
                                           (and 
                                               (exists ((i130 Int)) 
                                                   (and 
                                                       (<= 1 i130) 
                                                       (forall ((x1982 Int)) 
                                                           (=> 
                                                               (length p37 x1982) 
                                                               (<= i130 x1982))) 
                                                       (= x1980 i130) 
                                                       (exists ((x1983 Int)) 
                                                           (and 
                                                               (forall ((x1984 Int)) 
                                                                   (=> 
                                                                       (length p37 x1984) 
                                                                       (= x1983 (+ (- x1984 i130) 1)))) 
                                                               (MS1 x1983 x1981 p37))))) 
                                               (<= 1 x1980) 
                                               (forall ((x1985 Int)) 
                                                   (=> 
                                                       (length p37 x1985) 
                                                       (<= x1980 (- x1985 1)))))))))) 
                       (forall ((x1986 A)) 
                           (=> 
                               (exists ((x1987 Int)) 
                                   (and 
                                       (exists ((i131 Int)) 
                                           (and 
                                               (<= 1 i131) 
                                               (forall ((x1988 Int)) 
                                                   (=> 
                                                       (length p37 x1988) 
                                                       (<= i131 x1988))) 
                                               (= x1987 i131) 
                                               (exists ((x1989 Int)) 
                                                   (and 
                                                       (forall ((x1990 Int)) 
                                                           (=> 
                                                               (length p37 x1990) 
                                                               (= x1989 (+ (- x1990 i131) 1)))) 
                                                       (MS1 x1989 x1986 p37))))) 
                                       (<= 1 x1987) 
                                       (forall ((x1991 Int)) 
                                           (=> 
                                               (length p37 x1991) 
                                               (<= x1987 (- x1991 1)))))) 
                               (MS0 x1986 a))) 
                       (forall ((x1992 Int)) 
                           (=> 
                               (exists ((x1993 PZA)) 
                                   (and 
                                       (forall ((x1994 Int) (x1995 A)) 
                                           (= 
                                               (MS1 x1994 x1995 x1993) 
                                               (and 
                                                   (exists ((i132 Int)) 
                                                       (and 
                                                           (<= 1 i132) 
                                                           (forall ((x1996 Int)) 
                                                               (=> 
                                                                   (length p37 x1996) 
                                                                   (<= i132 x1996))) 
                                                           (= x1994 i132) 
                                                           (exists ((x1997 Int)) 
                                                               (and 
                                                                   (forall ((x1998 Int)) 
                                                                       (=> 
                                                                           (length p37 x1998) 
                                                                           (= x1997 (+ (- x1998 i132) 1)))) 
                                                                   (MS1 x1997 x1995 p37))))) 
                                                   (<= 1 x1994) 
                                                   (forall ((x1999 Int)) 
                                                       (=> 
                                                           (length p37 x1999) 
                                                           (<= x1994 (- x1999 1))))))) 
                                       (length x1993 x1992))) 
                               (< 1 x1992))) 
                       (exists ((i133 Int)) 
                           (and 
                               (<= 1 i133) 
                               (forall ((x2000 Int)) 
                                   (=> 
                                       (length p37 x2000) 
                                       (<= i133 x2000))) 
                               (= 1 i133) 
                               (exists ((x2001 Int)) 
                                   (and 
                                       (forall ((x2002 Int)) 
                                           (=> 
                                               (length p37 x2002) 
                                               (= x2001 (+ (- x2002 i133) 1)))) 
                                       (MS1 x2001 y212 p37))))) 
                       (<= 1 1) 
                       (forall ((x2003 Int)) 
                           (=> 
                               (length p37 x2003) 
                               (<= 1 (- x2003 1)))) 
                       (exists ((i134 Int)) 
                           (and 
                               (<= 1 i134) 
                               (forall ((x2004 Int)) 
                                   (=> 
                                       (length p37 x2004) 
                                       (<= i134 x2004))) 
                               (exists ((x2005 PZA)) 
                                   (and 
                                       (forall ((x2006 Int) (x2007 A)) 
                                           (= 
                                               (MS1 x2006 x2007 x2005) 
                                               (and 
                                                   (exists ((i135 Int)) 
                                                       (and 
                                                           (<= 1 i135) 
                                                           (forall ((x2008 Int)) 
                                                               (=> 
                                                                   (length p37 x2008) 
                                                                   (<= i135 x2008))) 
                                                           (= x2006 i135) 
                                                           (exists ((x2009 Int)) 
                                                               (and 
                                                                   (forall ((x2010 Int)) 
                                                                       (=> 
                                                                           (length p37 x2010) 
                                                                           (= x2009 (+ (- x2010 i135) 1)))) 
                                                                   (MS1 x2009 x2007 p37))))) 
                                                   (<= 1 x2006) 
                                                   (forall ((x2011 Int)) 
                                                       (=> 
                                                           (length p37 x2011) 
                                                           (<= x2006 (- x2011 1))))))) 
                                       (length x2005 i134))) 
                               (exists ((x2012 Int) (x2013 A)) 
                                   (and 
                                       (forall ((x2014 Int) (x2015 Int)) 
                                           (=> 
                                               (and 
                                                   (length p37 x2015) 
                                                   (length p37 x2014)) 
                                               (= x2012 (+ (- x2015 (- x2014 1)) 1)))) 
                                       (exists ((x2016 Int)) 
                                           (and 
                                               (forall ((x2017 Int)) 
                                                   (=> 
                                                       (length p37 x2017) 
                                                       (= x2016 (+ (- x2017 i134) 1)))) 
                                               (MS1 x2016 x2013 p37))) 
                                       (MS1 x2012 x2013 p37))))) 
                       (forall ((x2018 Int)) 
                           (=> 
                               (exists ((x2019 PZA)) 
                                   (and 
                                       (forall ((x2020 Int) (x2021 A)) 
                                           (= 
                                               (MS1 x2020 x2021 x2019) 
                                               (and 
                                                   (exists ((i136 Int)) 
                                                       (and 
                                                           (<= 1 i136) 
                                                           (forall ((x2022 Int)) 
                                                               (=> 
                                                                   (length p37 x2022) 
                                                                   (<= i136 x2022))) 
                                                           (= x2020 i136) 
                                                           (exists ((x2023 Int)) 
                                                               (and 
                                                                   (forall ((x2024 Int)) 
                                                                       (=> 
                                                                           (length p37 x2024) 
                                                                           (= x2023 (+ (- x2024 i136) 1)))) 
                                                                   (MS1 x2023 x2021 p37))))) 
                                                   (<= 1 x2020) 
                                                   (forall ((x2025 Int)) 
                                                       (=> 
                                                           (length p37 x2025) 
                                                           (<= x2020 (- x2025 1))))))) 
                                       (length x2019 x2018))) 
                               (<= 1 x2018))) 
                       (forall ((x2026 Int) (x2027 Int)) 
                           (=> 
                               (and 
                                   (exists ((x2028 PZA)) 
                                       (and 
                                           (forall ((x2029 Int) (x2030 A)) 
                                               (= 
                                                   (MS1 x2029 x2030 x2028) 
                                                   (and 
                                                       (exists ((i137 Int)) 
                                                           (and 
                                                               (<= 1 i137) 
                                                               (forall ((x2031 Int)) 
                                                                   (=> 
                                                                       (length p37 x2031) 
                                                                       (<= i137 x2031))) 
                                                               (= x2029 i137) 
                                                               (exists ((x2032 Int)) 
                                                                   (and 
                                                                       (forall ((x2033 Int)) 
                                                                           (=> 
                                                                               (length p37 x2033) 
                                                                               (= x2032 (+ (- x2033 i137) 1)))) 
                                                                       (MS1 x2032 x2030 p37))))) 
                                                       (<= 1 x2029) 
                                                       (forall ((x2034 Int)) 
                                                           (=> 
                                                               (length p37 x2034) 
                                                               (<= x2029 (- x2034 1))))))) 
                                           (length x2028 x2027))) 
                                   (length p37 x2026)) 
                               (<= x2027 (- x2026 1)))) 
                       (forall ((i138 Int)) 
                           (=> 
                               (and 
                                   (<= 1 i138) 
                                   (forall ((x2035 Int)) 
                                       (=> 
                                           (exists ((x2036 PZA)) 
                                               (and 
                                                   (forall ((x2037 Int) (x2038 A)) 
                                                       (= 
                                                           (MS1 x2037 x2038 x2036) 
                                                           (and 
                                                               (exists ((i139 Int)) 
                                                                   (and 
                                                                       (<= 1 i139) 
                                                                       (forall ((x2039 Int)) 
                                                                           (=> 
                                                                               (length p37 x2039) 
                                                                               (<= i139 x2039))) 
                                                                       (= x2037 i139) 
                                                                       (exists ((x2040 Int)) 
                                                                           (and 
                                                                               (forall ((x2041 Int)) 
                                                                                   (=> 
                                                                                       (length p37 x2041) 
                                                                                       (= x2040 (+ (- x2041 i139) 1)))) 
                                                                               (MS1 x2040 x2038 p37))))) 
                                                               (<= 1 x2037) 
                                                               (forall ((x2042 Int)) 
                                                                   (=> 
                                                                       (length p37 x2042) 
                                                                       (<= x2037 (- x2042 1))))))) 
                                                   (length x2036 x2035))) 
                                           (<= i138 (- x2035 1))))) 
                               (exists ((x2043 A) (x2044 A)) 
                                   (and 
                                       (exists ((i140 Int)) 
                                           (and 
                                               (<= 1 i140) 
                                               (forall ((x2045 Int)) 
                                                   (=> 
                                                       (length p37 x2045) 
                                                       (<= i140 x2045))) 
                                               (= i138 i140) 
                                               (exists ((x2046 Int)) 
                                                   (and 
                                                       (forall ((x2047 Int)) 
                                                           (=> 
                                                               (length p37 x2047) 
                                                               (= x2046 (+ (- x2047 i140) 1)))) 
                                                       (MS1 x2046 x2043 p37))))) 
                                       (<= 1 i138) 
                                       (forall ((x2048 Int)) 
                                           (=> 
                                               (length p37 x2048) 
                                               (<= i138 (- x2048 1)))) 
                                       (exists ((i141 Int)) 
                                           (and 
                                               (<= 1 i141) 
                                               (forall ((x2049 Int)) 
                                                   (=> 
                                                       (length p37 x2049) 
                                                       (<= i141 x2049))) 
                                               (= (+ i138 1) i141) 
                                               (exists ((x2050 Int)) 
                                                   (and 
                                                       (forall ((x2051 Int)) 
                                                           (=> 
                                                               (length p37 x2051) 
                                                               (= x2050 (+ (- x2051 i141) 1)))) 
                                                       (MS1 x2050 x2044 p37))))) 
                                       (<= 1 (+ i138 1)) 
                                       (forall ((x2052 Int)) 
                                           (=> 
                                               (length p37 x2052) 
                                               (<= (+ i138 1) (- x2052 1)))) 
                                       (MS x2043 x2044 r))))))))
         :named hyp119))
(assert (! (and 
               (<= 1 i) 
               (forall ((x2053 Int)) 
                   (=> 
                       (exists ((x2054 PZA)) 
                           (and 
                               (forall ((x2055 Int) (x2056 A)) 
                                   (= 
                                       (MS1 x2055 x2056 x2054) 
                                       (exists ((i142 Int)) 
                                           (and 
                                               (<= 1 i142) 
                                               (forall ((x2057 Int)) 
                                                   (=> 
                                                       (length p x2057) 
                                                       (<= i142 x2057))) 
                                               (= x2055 i142) 
                                               (exists ((x2058 Int)) 
                                                   (and 
                                                       (forall ((x2059 Int)) 
                                                           (=> 
                                                               (length p x2059) 
                                                               (= x2058 (+ (- x2059 i142) 1)))) 
                                                       (MS1 x2058 x2056 p))))))) 
                               (length x2054 x2053))) 
                       (<= i (- x2053 1)))))
         :named hyp120))
(assert (! (exists ((x2060 A) (x2061 Int)) 
               (and 
                   (exists ((x2062 Int)) 
                       (and 
                           (= x2062 1) 
                           (MS1 x2062 x2060 p))) 
                   (length p x2061) 
                   (dist x2060 y x2061)))
         :named hyp121))
(assert (! (exists ((x2063 A) (x2064 A) (x2065 Int)) 
               (and 
                   (exists ((x2066 Int)) 
                       (and 
                           (= x2066 1) 
                           (MS1 x2066 x2063 p))) 
                   (exists ((x2067 Int)) 
                       (and 
                           (length p x2067) 
                           (MS1 x2067 x2064 p))) 
                   (length p x2065) 
                   (dist x2063 x2064 x2065)))
         :named hyp122))
(assert (! (not 
               (exists ((x2068 A) (x2069 A)) 
                   (and 
                       (exists ((x2070 Int)) 
                           (and 
                               (forall ((x2071 Int)) 
                                   (=> 
                                       (length p x2071) 
                                       (= x2070 (+ (- x2071 i) 1)))) 
                               (MS1 x2070 x2068 p))) 
                       (exists ((x2072 Int)) 
                           (and 
                               (forall ((x2073 Int)) 
                                   (=> 
                                       (length p x2073) 
                                       (= x2072 (+ (- x2073 (+ i 1)) 1)))) 
                               (MS1 x2072 x2069 p))) 
                       (MS x2068 x2069 r))))
         :named goal))
(check-sat)
(exit)

