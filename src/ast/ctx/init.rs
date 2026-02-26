// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module is responsible for initializing the [Context] with theories. Modify this module
//! for other extensions.

use crate::allocator::{ObjectAllocatorExt, SortAllocator, StrAllocator};
use crate::ast::FunctionMeta;
use crate::ast::alg::BvLenExpr;
#[cfg(feature = "cnf")]
use crate::ast::cnf::CNFCache;
#[cfg(feature = "cache")]
use crate::ast::ctx::Caches;
use crate::ast::ctx::{Arena, BvInSort, BvOutSort, Sig, SigIndex, SortDef, Str, Theory};
use crate::ast::ctx::{Context, LOGICS};
use crate::statics::{ARRAY, BOOL};
use crate::traits::Repr;
use dashu::integer::UBig;
use std::collections::HashMap;

#[inline]
fn builtin(name: Str, sig: Sig) -> (Str, Vec<(Sig, FunctionMeta)>) {
    (name, vec![(sig, FunctionMeta::Opaque)])
}

#[inline]
fn builtins(name: Str, sigs: impl IntoIterator<Item = Sig>) -> (Str, Vec<(Sig, FunctionMeta)>) {
    (
        name,
        sigs.into_iter()
            .map(|s| (s, FunctionMeta::Opaque))
            .collect(),
    )
}

impl Context {
    fn default_sorts(arena: &mut Arena) -> HashMap<Str, SortDef> {
        let bool = arena.allocate_symbol(BOOL);
        HashMap::from([(bool, SortDef::Opaque(0))])
    }

    /// Create a new context to manipulate SMT
    pub fn new() -> Self {
        let mut arena = Arena::new();
        let sorts = Self::default_sorts(&mut arena);
        Self {
            arena,
            logic: None,
            sorts,
            symbol_table: Default::default(),
            #[cfg(feature = "cache")]
            caches: Caches {
                #[cfg(feature = "cnf")]
                cnf_cache: CNFCache::new(),
            },
        }
    }

    fn extend_theory_ints(&mut self) {
        let int = self.int_sort();
        self.sorts
            .insert(int.repr().0.symbol.clone(), SortDef::Opaque(0));

        let minus = self.allocate_symbol("-");
        let plus = self.allocate_symbol("+");
        let times = self.allocate_symbol("*");
        let div = self.allocate_symbol("div");
        let modd = self.allocate_symbol("mod");
        let abs = self.allocate_symbol("abs");
        let le = self.allocate_symbol("<=");
        let lt = self.allocate_symbol("<");
        let ge = self.allocate_symbol(">=");
        let gt = self.allocate_symbol(">");
        let one_or_more = Sig::VarLenFunc(int.clone(), 1, int.clone());
        let two_or_more = Sig::VarLenFunc(int.clone(), 2, int.clone());
        let unary_sig = Sig::func(vec![int.clone()], int.clone());
        let binary_sig = Sig::func(vec![int.clone(), int.clone()], int.clone());
        let bin_pred_sig = Sig::VarLenFunc(int.clone(), 2, self.bool_sort());
        let default_symbol_table = HashMap::from([
            builtin(minus, one_or_more),
            builtin(plus, two_or_more.clone()),
            builtin(times, two_or_more.clone()),
            builtin(div, two_or_more.clone()),
            builtin(modd, binary_sig.clone()),
            builtin(abs, unary_sig.clone()),
            builtin(le, bin_pred_sig.clone()),
            builtin(lt, bin_pred_sig.clone()),
            builtin(ge, bin_pred_sig.clone()),
            builtin(gt, bin_pred_sig.clone()),
        ]);
        self.symbol_table.extend(default_symbol_table);
    }

    fn extend_theory_reals(&mut self) {
        let real = self.real_sort();
        self.sorts
            .insert(real.repr().0.symbol.clone(), SortDef::Opaque(0));
        let minus = self.allocate_symbol("-");
        let plus = self.allocate_symbol("+");
        let times = self.allocate_symbol("*");
        let real_div = self.allocate_symbol("/");
        let le = self.allocate_symbol("<=");
        let lt = self.allocate_symbol("<");
        let ge = self.allocate_symbol(">=");
        let gt = self.allocate_symbol(">");
        let one_or_more = Sig::VarLenFunc(real.clone(), 1, real.clone());
        let two_or_more = Sig::VarLenFunc(real.clone(), 2, real.clone());
        let bin_pred_sig = Sig::VarLenFunc(real.clone(), 2, self.bool_sort());
        let default_symbol_table = HashMap::from([
            builtin(minus, one_or_more.clone()),
            builtin(plus, two_or_more.clone()),
            builtin(times, two_or_more.clone()),
            builtin(real_div, two_or_more),
            builtin(le, bin_pred_sig.clone()),
            builtin(lt, bin_pred_sig.clone()),
            builtin(ge, bin_pred_sig.clone()),
            builtin(gt, bin_pred_sig.clone()),
        ]);
        self.symbol_table.extend(default_symbol_table);
    }

    fn extend_theory_real_ints(&mut self) {
        let int = self.int_sort();
        let real = self.real_sort();
        self.sorts
            .insert(int.repr().0.symbol.clone(), SortDef::Opaque(0));
        self.sorts
            .insert(real.repr().0.symbol.clone(), SortDef::Opaque(0));

        let minus = self.allocate_symbol("-");
        let plus = self.allocate_symbol("+");
        let times = self.allocate_symbol("*");
        let div = self.allocate_symbol("div");
        let real_div = self.allocate_symbol("/");
        let modd = self.allocate_symbol("mod");
        let abs = self.allocate_symbol("abs");
        let le = self.allocate_symbol("<=");
        let lt = self.allocate_symbol("<");
        let ge = self.allocate_symbol(">=");
        let gt = self.allocate_symbol(">");
        let to_real = self.allocate_symbol("to_real");
        let to_int = self.allocate_symbol("to_int");
        let is_int = self.allocate_symbol("is_int");
        let unary_sig = Sig::func(vec![int.clone()], int.clone());
        let two_ints = Sig::func(vec![int.clone(), int.clone()], int.clone());
        let two_or_more_ints = Sig::VarLenFunc(int.clone(), 2, int.clone());
        let two_or_more_reals = Sig::VarLenFunc(real.clone(), 2, real.clone());
        let one_or_more = [
            Sig::VarLenFunc(int.clone(), 1, int.clone()),
            Sig::VarLenFunc(real.clone(), 1, real.clone()),
        ];
        let two_or_more = [
            Sig::VarLenFunc(int.clone(), 2, int.clone()),
            Sig::VarLenFunc(real.clone(), 2, real.clone()),
        ];
        let bin_pred_sig = [
            Sig::VarLenFunc(int.clone(), 2, self.bool_sort()),
            Sig::VarLenFunc(real.clone(), 2, self.bool_sort()),
        ];
        let default_symbol_table = HashMap::from([
            builtins(minus, one_or_more),
            builtins(plus, two_or_more.clone()),
            builtins(times, two_or_more.clone()),
            builtin(div, two_or_more_ints.clone()),
            builtin(real_div, two_or_more_reals.clone()),
            builtin(modd, two_ints.clone()),
            builtin(abs, unary_sig.clone()),
            builtins(le, bin_pred_sig.clone()),
            builtins(lt, bin_pred_sig.clone()),
            builtins(ge, bin_pred_sig.clone()),
            builtins(gt, bin_pred_sig.clone()),
            builtin(to_real, Sig::func(vec![int.clone()], real.clone())),
            builtin(to_int, Sig::func(vec![real.clone()], int.clone())),
            builtin(is_int, Sig::func(vec![real.clone()], self.bool_sort())),
        ]);
        self.symbol_table.extend(default_symbol_table);
    }

    fn extend_theory_strings(&mut self) {
        let string = self.string_sort();
        let reglan = self.reglan_sort();
        let int = self.int_sort();
        let bool = self.bool_sort();

        self.sorts
            .insert(string.repr().0.symbol.clone(), SortDef::Opaque(0));
        self.sorts
            .insert(int.repr().0.symbol.clone(), SortDef::Opaque(0));
        self.sorts
            .insert(reglan.repr().0.symbol.clone(), SortDef::Opaque(0));

        let str_unary_sig = Sig::func(vec![string.clone()], int.clone());
        let str_binary_sig = Sig::VarLenFunc(string.clone(), 2, string.clone());
        let str_ternary_sig = Sig::func(
            vec![string.clone(), string.clone(), string.clone()],
            string.clone(),
        );
        let str_unary_pred = Sig::func(vec![string.clone()], bool.clone());
        let str_binary_more_pred = Sig::VarLenFunc(string.clone(), 2, bool.clone());
        let str_binary_pred = Sig::func(vec![string.clone(), string.clone()], bool.clone());
        let replace_sig = Sig::func(
            vec![string.clone(), reglan.clone(), string.clone()],
            string.clone(),
        );
        let re_unary_sig = Sig::func(vec![reglan.clone()], reglan.clone());
        let re_binary_sig = Sig::VarLenFunc(reglan.clone(), 2, reglan.clone());

        let char = self.allocate_symbol("char");

        let str_pp = self.allocate_symbol("str.++");
        let str_len = self.allocate_symbol("str.len");
        let str_lt = self.allocate_symbol("str.<");
        let str_to_re = self.allocate_symbol("str.to_re");
        let str_in_re = self.allocate_symbol("str.in_re");
        let re_none = self.allocate_symbol("re.none");
        let re_all = self.allocate_symbol("re.all");
        let re_allchar = self.allocate_symbol("re.allchar");
        let re_pp = self.allocate_symbol("re.++");
        let re_union = self.allocate_symbol("re.union");
        let re_inter = self.allocate_symbol("re.inter");
        let re_star = self.allocate_symbol("re.*");

        // additional functions
        let str_le = self.allocate_symbol("str.<=");
        let str_at = self.allocate_symbol("str.at");
        let str_substr = self.allocate_symbol("str.substr");
        let str_prefixof = self.allocate_symbol("str.prefixof");
        let str_suffixof = self.allocate_symbol("str.suffixof");
        let str_contains = self.allocate_symbol("str.contains");
        let str_indexof = self.allocate_symbol("str.indexof");
        let str_replace = self.allocate_symbol("str.replace");
        let str_replace_all = self.allocate_symbol("str.replace_all");
        let str_replace_re = self.allocate_symbol("str.replace_re");
        let str_replace_re_all = self.allocate_symbol("str.replace_re_all");
        let re_comp = self.allocate_symbol("re.comp");
        let re_diff = self.allocate_symbol("re.diff");
        let re_p = self.allocate_symbol("re.+");
        let re_opt = self.allocate_symbol("re.opt");
        let re_range = self.allocate_symbol("re.range");
        let re_hat = self.allocate_symbol("re.^");
        let re_loop = self.allocate_symbol("re.loop");

        let str_is_digit = self.allocate_symbol("str.is_digit");
        let str_to_code = self.allocate_symbol("str.to_code");
        let str_from_code = self.allocate_symbol("str.from_code");
        let str_to_int = self.allocate_symbol("str.to_int");
        let str_from_int = self.allocate_symbol("str_from_int");

        let default_symbol_table = HashMap::from([
            builtin(
                char,
                Sig::ParFunc(vec![SigIndex::Hexadecimal], vec![], vec![], string.clone()),
            ),
            builtin(str_pp, str_binary_sig.clone()),
            builtin(str_len, str_unary_sig),
            builtin(str_lt, str_binary_more_pred.clone()),
            builtin(str_to_re, Sig::func(vec![string.clone()], reglan.clone())),
            builtin(
                str_in_re,
                Sig::func(vec![string.clone(), reglan.clone()], bool.clone()),
            ),
            builtin(re_none, Sig::sort(reglan.clone())),
            builtin(re_all, Sig::sort(reglan.clone())),
            builtin(re_allchar, Sig::sort(reglan.clone())),
            builtin(re_pp, re_binary_sig.clone()),
            builtin(re_union, re_binary_sig.clone()),
            builtin(re_inter, re_binary_sig.clone()),
            builtin(re_star, re_unary_sig.clone()),
            builtin(str_le, str_binary_more_pred.clone()),
            builtin(
                str_at,
                Sig::func(vec![string.clone(), int.clone()], string.clone()),
            ),
            builtin(
                str_substr,
                Sig::func(
                    vec![string.clone(), int.clone(), int.clone()],
                    string.clone(),
                ),
            ),
            builtin(str_prefixof, str_binary_pred.clone()),
            builtin(str_suffixof, str_binary_pred.clone()),
            builtin(str_contains, str_binary_pred.clone()),
            builtin(
                str_indexof,
                Sig::func(
                    vec![string.clone(), string.clone(), int.clone()],
                    int.clone(),
                ),
            ),
            builtin(str_replace, str_ternary_sig.clone()),
            builtin(str_replace_all, str_ternary_sig.clone()),
            builtin(str_replace_re, replace_sig.clone()),
            builtin(str_replace_re_all, replace_sig.clone()),
            builtin(re_comp, Sig::func(vec![reglan.clone()], reglan.clone())),
            builtin(re_diff, re_binary_sig.clone()),
            builtin(re_p, re_unary_sig.clone()),
            builtin(re_opt, re_unary_sig.clone()),
            builtin(
                re_range,
                Sig::func(vec![string.clone(), string.clone()], reglan.clone()),
            ),
            builtin(
                re_hat,
                Sig::ParFunc(
                    vec![SigIndex::Numeral],
                    vec![],
                    vec![reglan.clone()],
                    reglan.clone(),
                ),
            ),
            builtin(
                re_loop,
                Sig::ParFunc(
                    vec![SigIndex::Numeral, SigIndex::Numeral],
                    vec![],
                    vec![reglan.clone()],
                    reglan.clone(),
                ),
            ),
            builtin(str_is_digit, str_unary_pred.clone()),
            builtin(str_to_code, Sig::func(vec![string.clone()], int.clone())),
            builtin(str_from_code, Sig::func(vec![int.clone()], string.clone())),
            builtin(str_to_int, Sig::func(vec![string.clone()], int.clone())),
            builtin(str_from_int, Sig::func(vec![int.clone()], string.clone())),
        ]);
        self.symbol_table.extend(default_symbol_table);
    }

    fn extend_theory_array_ex(&mut self) {
        let array = self.allocate_symbol(ARRAY);
        self.sorts.insert(array, SortDef::Opaque(2));

        let x = self.allocate_symbol("X");
        let y = self.allocate_symbol("Y");
        let vars = vec![x.clone(), y.clone()];
        let sort_x = self.simple_sort("X");
        let sort_y = self.simple_sort("Y");
        let array_xy = self.array_sort(sort_x.clone(), sort_y.clone());

        let select = self.allocate_symbol("select");
        let store = self.allocate_symbol("store");

        let default_symbol_table = HashMap::from([
            builtin(
                select,
                Sig::ParFunc(
                    vec![],
                    vars.clone(),
                    vec![array_xy.clone(), sort_x.clone()],
                    sort_y.clone(),
                ),
            ),
            builtin(
                store,
                Sig::ParFunc(
                    vec![],
                    vars,
                    vec![array_xy.clone(), sort_x, sort_y],
                    array_xy,
                ),
            ),
        ]);
        self.symbol_table.extend(default_symbol_table);
    }

    fn extend_theory_floating_points(&mut self) {
        // todo: the floating point theory is incomplete

        let rm = self.allocate_symbol("RoundingMode");
        let float16 = self.allocate_symbol("Float16");
        let float32 = self.allocate_symbol("Float32");
        let float64 = self.allocate_symbol("Float64");
        let float128 = self.allocate_symbol("Float128");
        self.sorts.insert(rm.clone(), SortDef::Opaque(0));
        self.sorts.insert(float16.clone(), SortDef::Opaque(0));
        self.sorts.insert(float32.clone(), SortDef::Opaque(0));
        self.sorts.insert(float64.clone(), SortDef::Opaque(0));
        self.sorts.insert(float128.clone(), SortDef::Opaque(0));

        let rm = self.sort0(rm);
        let rm = Sig::sort(rm);
        let rnte = self.allocate_symbol("roundNearestTiesToEven");
        let rnta = self.allocate_symbol("roundNearestTiesToAway");
        let rntp = self.allocate_symbol("roundTowardPositive");
        let rntn = self.allocate_symbol("roundTowardNegative");
        let rntz = self.allocate_symbol("roundTowardZero");
        let rne = self.allocate_symbol("RNE");
        let rna = self.allocate_symbol("RNA");
        let rtp = self.allocate_symbol("RTP");
        let rtn = self.allocate_symbol("RTN");
        let rtz = self.allocate_symbol("RTZ");

        let default_symbol_table = HashMap::from([
            builtin(rnte, rm.clone()),
            builtin(rnta, rm.clone()),
            builtin(rntp, rm.clone()),
            builtin(rntn, rm.clone()),
            builtin(rntz, rm.clone()),
            builtin(rne, rm.clone()),
            builtin(rna, rm.clone()),
            builtin(rtp, rm.clone()),
            builtin(rtn, rm.clone()),
            builtin(rtz, rm.clone()),
        ]);
        self.symbol_table.extend(default_symbol_table);
    }

    /// c.f. <https://smt-lib.org/logics-all.shtml#QF_BV> and <https://smt-lib.org/theories-FixedSizeBitVectors.shtml>
    fn extend_theory_bitvectors(&mut self) {
        let int = self.int_sort();
        let bool = self.bool_sort();
        let bv1 = self.bv_sort(UBig::from(1u8));

        let concat = self.allocate_symbol("concat");
        let extract = self.allocate_symbol("extract");
        let bvnot = self.allocate_symbol("bvnot");
        let bvneg = self.allocate_symbol("bvneg");
        let bvand = self.allocate_symbol("bvand");
        let bvor = self.allocate_symbol("bvor");
        let bvadd = self.allocate_symbol("bvadd");
        let bvmul = self.allocate_symbol("bvmul");
        let bvudiv = self.allocate_symbol("bvudiv");
        let bvurem = self.allocate_symbol("bvurem");
        let bvshl = self.allocate_symbol("bvshl");
        let bvlshr = self.allocate_symbol("bvlshr");
        let bvult = self.allocate_symbol("bvult");
        let bvnego = self.allocate_symbol("bvnego");
        let bvuaddo = self.allocate_symbol("bvuaddo");
        let bvsaddo = self.allocate_symbol("bvsaddo");
        let bvumulo = self.allocate_symbol("bvumulo");
        let bvsmulo = self.allocate_symbol("bvsmulo");

        let ubv_to_int = self.allocate_symbol("ubv_to_int");
        let sbv_to_int = self.allocate_symbol("sbv_to_int");
        let bv2nat = self.allocate_symbol("bv2nat");
        let bv2int = self.allocate_symbol("bv2int");
        let int_to_bv = self.allocate_symbol("int_to_bv");
        let nat2bv = self.allocate_symbol("nat2bv");
        let int2bv = self.allocate_symbol("int2bv");

        let bvnand = self.allocate_symbol("bvnand");
        let bvnor = self.allocate_symbol("bvnor");
        let bvxor = self.allocate_symbol("bvxor");
        let bvxnor = self.allocate_symbol("bvxnor");
        let bvcomp = self.allocate_symbol("bvcomp");
        let bvsub = self.allocate_symbol("bvsub");
        let bvsdiv = self.allocate_symbol("bvsdiv");
        let bvsrem = self.allocate_symbol("bvsrem");
        let bvsmod = self.allocate_symbol("bvsmod");
        let bvashr = self.allocate_symbol("bvashr");
        let bvusubo = self.allocate_symbol("bvusubo");
        let bvssubo = self.allocate_symbol("bvssubo");
        let bvsdivo = self.allocate_symbol("bvsdivo");

        let repeat = self.allocate_symbol("repeat");
        let zero_extend = self.allocate_symbol("zero_extend");
        let sign_extend = self.allocate_symbol("sign_extend");
        let rotate_left = self.allocate_symbol("rotate_left");
        let rotate_right = self.allocate_symbol("rotate_right");

        let bvule = self.allocate_symbol("bvule");
        let bvugt = self.allocate_symbol("bvugt");
        let bvuge = self.allocate_symbol("bvuge");
        let bvslt = self.allocate_symbol("bvslt");
        let bvsle = self.allocate_symbol("bvsle");
        let bvsgt = self.allocate_symbol("bvsgt");
        let bvsge = self.allocate_symbol("bvsge");

        let opt1_sig = Sig::BvFunc(0, 1, false, vec![BvInSort::BitVec(0)], BvOutSort::bv_var(0));
        let opt2_sig = Sig::BvFunc(
            0,
            1,
            false,
            vec![BvInSort::BitVec(0), BvInSort::BitVec(0)],
            BvOutSort::bv_var(0),
        );
        let opt2_sig_lassoc = Sig::BvVarLenFunc(1, BvInSort::BitVec(0), 2, BvOutSort::bv_var(0));
        let un_pred_sig = Sig::BvFunc(
            0,
            1,
            false,
            vec![BvInSort::BitVec(0)],
            BvOutSort::Sort(bool.clone()),
        );
        let bin_pred_sig = Sig::BvFunc(
            0,
            1,
            false,
            vec![BvInSort::BitVec(0), BvInSort::BitVec(0)],
            BvOutSort::Sort(bool.clone()),
        );
        let to_int_sig = Sig::BvFunc(
            0,
            1,
            false,
            vec![BvInSort::BitVec(0)],
            BvOutSort::Sort(int.clone()),
        );
        let to_bv_sig = Sig::BvFunc(
            1,
            0,
            false,
            vec![BvInSort::Sort(int.clone())],
            BvOutSort::bv_var(0),
        );
        let extend_sig = Sig::BvFunc(
            1,
            1,
            false,
            vec![BvInSort::BitVec(1)],
            BvOutSort::BitVec(BvLenExpr::var(0) + BvLenExpr::var(1)),
        );
        let rotate_sig = Sig::BvFunc(
            1,
            1,
            false,
            vec![BvInSort::BitVec(1)],
            BvOutSort::BitVec(BvLenExpr::var(1)),
        );

        let default_symbol_table = HashMap::from([
            builtin(concat, Sig::BvConcat),
            builtin(
                extract,
                Sig::BvFunc(
                    2,
                    1,
                    true,
                    vec![BvInSort::BitVec(2)],
                    BvOutSort::BitVec(BvLenExpr::var(0) + BvLenExpr::fixed(1) - BvLenExpr::var(1)),
                ),
            ),
            builtin(bvnot, opt1_sig.clone()),
            builtin(bvneg, opt1_sig.clone()),
            // the spec only explicitly mention left associativity for the next five
            builtin(bvand, opt2_sig_lassoc.clone()),
            builtin(bvor, opt2_sig_lassoc.clone()),
            builtin(bvadd, opt2_sig_lassoc.clone()),
            builtin(bvmul, opt2_sig_lassoc.clone()),
            builtin(bvxor, opt2_sig_lassoc.clone()),
            builtin(bvudiv, opt2_sig.clone()),
            builtin(bvurem, opt2_sig.clone()),
            builtin(bvshl, opt2_sig.clone()),
            builtin(bvlshr, opt2_sig.clone()),
            builtin(bvult, bin_pred_sig.clone()),
            builtin(bvnego, un_pred_sig.clone()),
            builtin(bvuaddo, bin_pred_sig.clone()),
            builtin(bvsaddo, bin_pred_sig.clone()),
            builtin(bvumulo, bin_pred_sig.clone()),
            builtin(bvsmulo, bin_pred_sig.clone()),
            builtin(bvnand, opt2_sig.clone()),
            builtin(bvnor, opt2_sig.clone()),
            builtin(bvxnor, opt2_sig.clone()),
            builtin(
                bvcomp,
                Sig::BvFunc(
                    0,
                    1,
                    false,
                    vec![BvInSort::BitVec(0), BvInSort::BitVec(0)],
                    BvOutSort::Sort(bv1),
                ),
            ),
            builtin(bvsub, opt2_sig.clone()),
            builtin(bvsdiv, opt2_sig.clone()),
            builtin(bvsrem, opt2_sig.clone()),
            builtin(bvsmod, opt2_sig.clone()),
            builtin(bvashr, opt2_sig.clone()),
            builtin(bvusubo, bin_pred_sig.clone()),
            builtin(bvssubo, bin_pred_sig.clone()),
            builtin(bvsdivo, bin_pred_sig.clone()),
            builtin(
                repeat,
                Sig::BvFunc(
                    1,
                    1,
                    false,
                    vec![BvInSort::BitVec(1)],
                    BvOutSort::BitVec(BvLenExpr::var(0) * BvLenExpr::var(1)),
                ),
            ),
            builtin(zero_extend, extend_sig.clone()),
            builtin(sign_extend, extend_sig.clone()),
            builtin(rotate_left, rotate_sig.clone()),
            builtin(rotate_right, rotate_sig.clone()),
            builtin(bvule, bin_pred_sig.clone()),
            builtin(bvugt, bin_pred_sig.clone()),
            builtin(bvuge, bin_pred_sig.clone()),
            builtin(bvslt, bin_pred_sig.clone()),
            builtin(bvsle, bin_pred_sig.clone()),
            builtin(bvsgt, bin_pred_sig.clone()),
            builtin(bvsge, bin_pred_sig.clone()),
        ]);
        self.symbol_table.extend(default_symbol_table);

        if self.get_theories().iter().any(|t| t.has_int()) {
            let more_symbols = HashMap::from([
                builtin(ubv_to_int, to_int_sig.clone()),
                builtin(sbv_to_int, to_int_sig.clone()),
                builtin(bv2int, to_int_sig.clone()),
                builtin(bv2nat, to_int_sig.clone()),
                builtin(int_to_bv, to_bv_sig.clone()),
                builtin(nat2bv, to_bv_sig.clone()),
                builtin(int2bv, to_bv_sig.clone()),
            ]);

            self.symbol_table.extend(more_symbols);
        }
    }

    pub fn check_logic(&self) -> Result<(), String> {
        if self.logic.is_none() {
            Err("logic is not set".into())
        } else {
            Ok(())
        }
    }

    pub fn check_support_theory(&self, theory: Theory) -> Result<(), String> {
        if self.get_theories().contains(&theory) {
            Ok(())
        } else {
            Err(format!(
                "TC: the current logic does not support the theory of {theory}!"
            ))
        }
    }

    /// set the current theory; error if current theory has been set
    pub fn set_ctx_logic(&mut self, s: &str) -> Result<&mut Self, String> {
        match &self.logic {
            None => match LOGICS.get(s.to_ascii_uppercase().as_str()) {
                None => Err(format!("Theory {} not defined", s)),
                Some(ts) => {
                    self.logic = Some(s.to_string());
                    for t in ts {
                        match t {
                            Theory::Quantifiers => {}
                            Theory::Ints => self.extend_theory_ints(),
                            Theory::Reals => self.extend_theory_reals(),
                            Theory::RealInts => self.extend_theory_real_ints(),
                            Theory::Strings => self.extend_theory_strings(),
                            Theory::ArrayEx => self.extend_theory_array_ex(),
                            Theory::FloatingPoints => self.extend_theory_floating_points(),
                            Theory::Bitvectors => self.extend_theory_bitvectors(),
                            Theory::Datatypes => {}
                        }
                    }
                    Ok(self)
                }
            },
            Some(l) => Err(format!("Current logic has been set to {}", l)),
        }
    }

    /// make sure logic is set; if not, set it to ALL
    pub fn ensure_logic(&mut self) {
        if self.logic.is_none() {
            self.set_ctx_logic("ALL").unwrap();
        }
    }
}
