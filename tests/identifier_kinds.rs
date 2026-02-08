use dashu::integer::UBig;
use yaspar::tokens::Token;
use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{
    Context, HasArena, Identifier, IdentifierKind, Index, QualifiedIdentifier, StrAllocator,
};

fn test_simple_kind<T>(context: &mut T, kind: IdentifierKind)
where
    T: HasArena,
{
    let name = context.arena().allocate_symbol(kind.name());
    let identifier = QualifiedIdentifier::simple(name);
    assert_eq!(identifier.get_kind(), Some(kind));
}

fn test_kind_one_idx<T, F>(context: &mut T, kind_f: F, idx: UBig)
where
    T: HasArena,
    F: Fn(UBig) -> IdentifierKind,
{
    let kind = kind_f(idx.clone());
    let symbol = context.arena().allocate_symbol(kind.name());
    let identifier: QualifiedIdentifier = Identifier {
        symbol,
        indices: vec![Index::Numeral(idx)],
    }
    .into();
    assert_eq!(identifier.get_kind(), Some(kind));
}

fn test_kind_two_idx<T, F>(context: &mut T, kind_f: F, idx1: UBig, idx2: UBig)
where
    T: HasArena,
    F: Fn(UBig, UBig) -> IdentifierKind,
{
    let kind = kind_f(idx1.clone(), idx2.clone());
    let symbol = context.arena().allocate_symbol(kind.name());
    let identifier: QualifiedIdentifier = Identifier {
        symbol,
        indices: vec![Index::Numeral(idx1), Index::Numeral(idx2)],
    }
    .into();
    assert_eq!(identifier.get_kind(), Some(kind));
}

#[test]
fn test_identifier_kinds() {
    let mut context = Context::default();

    test_simple_kind(&mut context, IdentifierKind::And);
    test_simple_kind(&mut context, IdentifierKind::Or);
    test_simple_kind(&mut context, IdentifierKind::Not);
    test_simple_kind(&mut context, IdentifierKind::Implies);
    test_simple_kind(&mut context, IdentifierKind::Xor);
    test_simple_kind(&mut context, IdentifierKind::Eq);
    test_simple_kind(&mut context, IdentifierKind::Distinct);
    test_simple_kind(&mut context, IdentifierKind::Ite);
    test_simple_kind(&mut context, IdentifierKind::Select);
    test_simple_kind(&mut context, IdentifierKind::Store);
    test_simple_kind(&mut context, IdentifierKind::Add);
    test_simple_kind(&mut context, IdentifierKind::Sub);
    test_simple_kind(&mut context, IdentifierKind::Mul);
    test_simple_kind(&mut context, IdentifierKind::Idiv);
    test_simple_kind(&mut context, IdentifierKind::Rdiv);
    test_simple_kind(&mut context, IdentifierKind::Mod);
    test_simple_kind(&mut context, IdentifierKind::Abs);
    test_simple_kind(&mut context, IdentifierKind::Le);
    test_simple_kind(&mut context, IdentifierKind::Lt);
    test_simple_kind(&mut context, IdentifierKind::Ge);
    test_simple_kind(&mut context, IdentifierKind::Gt);
    test_simple_kind(&mut context, IdentifierKind::ToReal);
    test_simple_kind(&mut context, IdentifierKind::ToInt);
    test_simple_kind(&mut context, IdentifierKind::IsInt);
    test_simple_kind(&mut context, IdentifierKind::StrConcat);
    test_simple_kind(&mut context, IdentifierKind::StrLen);
    test_simple_kind(&mut context, IdentifierKind::StrLt);
    test_simple_kind(&mut context, IdentifierKind::StrToRe);
    test_simple_kind(&mut context, IdentifierKind::StrInRe);
    test_simple_kind(&mut context, IdentifierKind::ReNone);
    test_simple_kind(&mut context, IdentifierKind::ReAll);
    test_simple_kind(&mut context, IdentifierKind::ReAllChar);
    test_simple_kind(&mut context, IdentifierKind::ReConcat);
    test_simple_kind(&mut context, IdentifierKind::ReUnion);
    test_simple_kind(&mut context, IdentifierKind::ReInter);
    test_simple_kind(&mut context, IdentifierKind::ReStar);
    test_simple_kind(&mut context, IdentifierKind::StrLe);
    test_simple_kind(&mut context, IdentifierKind::StrAt);
    test_simple_kind(&mut context, IdentifierKind::StrSubstr);
    test_simple_kind(&mut context, IdentifierKind::StrPrefixof);
    test_simple_kind(&mut context, IdentifierKind::StrSuffixof);
    test_simple_kind(&mut context, IdentifierKind::StrContains);
    test_simple_kind(&mut context, IdentifierKind::StrIndexof);
    test_simple_kind(&mut context, IdentifierKind::StrReplace);
    test_simple_kind(&mut context, IdentifierKind::StrReplaceAll);
    test_simple_kind(&mut context, IdentifierKind::StrReplaceRe);
    test_simple_kind(&mut context, IdentifierKind::StrReplaceReAll);
    test_simple_kind(&mut context, IdentifierKind::ReComp);
    test_simple_kind(&mut context, IdentifierKind::ReDiff);
    test_simple_kind(&mut context, IdentifierKind::ReAdd);
    test_simple_kind(&mut context, IdentifierKind::ReOpt);
    test_simple_kind(&mut context, IdentifierKind::ReRange);
    test_simple_kind(&mut context, IdentifierKind::StrIsDigit);
    test_simple_kind(&mut context, IdentifierKind::StrToCode);
    test_simple_kind(&mut context, IdentifierKind::StrFromCode);
    test_simple_kind(&mut context, IdentifierKind::StrToInt);
    test_simple_kind(&mut context, IdentifierKind::StrFromInt);
    test_simple_kind(&mut context, IdentifierKind::Concat);
    test_simple_kind(&mut context, IdentifierKind::BvNot);
    test_simple_kind(&mut context, IdentifierKind::BvNeg);
    test_simple_kind(&mut context, IdentifierKind::BvAnd);
    test_simple_kind(&mut context, IdentifierKind::BvOr);
    test_simple_kind(&mut context, IdentifierKind::BvAdd);
    test_simple_kind(&mut context, IdentifierKind::BvMul);
    test_simple_kind(&mut context, IdentifierKind::BvUdiv);
    test_simple_kind(&mut context, IdentifierKind::BvUrem);
    test_simple_kind(&mut context, IdentifierKind::BvShl);
    test_simple_kind(&mut context, IdentifierKind::BvLshr);
    test_simple_kind(&mut context, IdentifierKind::BvUlt);
    test_simple_kind(&mut context, IdentifierKind::BvNego);
    test_simple_kind(&mut context, IdentifierKind::BvUaddo);
    test_simple_kind(&mut context, IdentifierKind::BvSaddo);
    test_simple_kind(&mut context, IdentifierKind::BvUmulo);
    test_simple_kind(&mut context, IdentifierKind::BvSmulo);
    test_simple_kind(&mut context, IdentifierKind::UbvToInt);
    test_simple_kind(&mut context, IdentifierKind::SbvToInt);
    test_simple_kind(&mut context, IdentifierKind::Bv2Nat);
    test_simple_kind(&mut context, IdentifierKind::Bv2Int);
    test_simple_kind(&mut context, IdentifierKind::BvNand);
    test_simple_kind(&mut context, IdentifierKind::BvNor);
    test_simple_kind(&mut context, IdentifierKind::BvXor);
    test_simple_kind(&mut context, IdentifierKind::BvNxor);
    test_simple_kind(&mut context, IdentifierKind::BvComp);
    test_simple_kind(&mut context, IdentifierKind::BvSub);
    test_simple_kind(&mut context, IdentifierKind::BvSdiv);
    test_simple_kind(&mut context, IdentifierKind::BvSrem);
    test_simple_kind(&mut context, IdentifierKind::BvSmod);
    test_simple_kind(&mut context, IdentifierKind::BvAShr);
    test_simple_kind(&mut context, IdentifierKind::BvUsubo);
    test_simple_kind(&mut context, IdentifierKind::BvSsubo);
    test_simple_kind(&mut context, IdentifierKind::BvSdivo);
    test_simple_kind(&mut context, IdentifierKind::BvUle);
    test_simple_kind(&mut context, IdentifierKind::BvUgt);
    test_simple_kind(&mut context, IdentifierKind::BvUge);
    test_simple_kind(&mut context, IdentifierKind::BvSlt);
    test_simple_kind(&mut context, IdentifierKind::BvSle);
    test_simple_kind(&mut context, IdentifierKind::BvSgt);
    test_simple_kind(&mut context, IdentifierKind::BvSge);

    test_kind_one_idx(&mut context, IdentifierKind::RePower, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::IntToBv, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::Nat2Bv, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::Int2Bv, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::Repeat, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::ZeroExtend, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::SignExtend, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::RotateLeft, UBig::from(1u8));
    test_kind_one_idx(&mut context, IdentifierKind::RotateRight, UBig::from(1u8));

    test_kind_two_idx(
        &mut context,
        IdentifierKind::ReLoop,
        UBig::from(1u8),
        UBig::from(2u8),
    );
    test_kind_two_idx(
        &mut context,
        IdentifierKind::Extract,
        UBig::from(1u8),
        UBig::from(2u8),
    );

    let mut tok = yaspar::tokenize_str("#xaB", false);
    let (bytes, len) = match tok.next() {
        Some(Ok((_, Token::Hexadecimal(tup), _))) => tup,
        _ => {
            panic!()
        }
    };
    let kind = IdentifierKind::Char(bytes.clone(), len);
    let symbol = context.arena().allocate_symbol(kind.name());
    let identifier: QualifiedIdentifier = Identifier {
        symbol,
        indices: vec![Index::Hexadecimal(bytes, len)],
    }
    .into();
    assert_eq!(identifier.get_kind(), Some(kind));

    let foo = context.allocate_symbol("foo");
    let kind = IdentifierKind::Is(foo.clone());
    let symbol = context.arena().allocate_symbol(kind.name());
    let identifier: QualifiedIdentifier = Identifier {
        symbol,
        indices: vec![Index::Symbol(foo)],
    }
    .into();
    assert_eq!(identifier.get_kind(), Some(kind));
}
