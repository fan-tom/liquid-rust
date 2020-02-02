#[test]
fn test() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/no-attributes.rs");
    t.pass("tests/ui/precondition-satisfied.rs");
    t.compile_fail("tests/ui/precondition-unsatisfied.rs");
}