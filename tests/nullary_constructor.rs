use yaspar_ir::ast::{CheckedApi, Context, Typecheck};
use yaspar_ir::untyped::UntypedAst;

/// Regression test: when a nullary constructor is applied via `typed_simp_app`,
/// Display must emit just the symbol name, not `(Name )` with a trailing space.
#[test]
fn nullary_constructor_app_no_trailing_space() {
    let mut ctx = Context::new();
    ctx.ensure_logic();

    // Declare a datatype with a nullary constructor
    let cmd = UntypedAst
        .parse_command_str("(declare-datatype Color ((Red) (Green) (Blue)))")
        .unwrap();
    cmd.type_check(&mut ctx).unwrap();

    // Apply the nullary constructor via the typed API (same path the solver client uses)
    let term = ctx.typed_simp_app("Red", std::iter::empty()).unwrap();

    let output = format!("{}", term);
    assert_eq!(
        output, "Red",
        "nullary constructor application should print as bare symbol, got: `{output}`"
    );
}
