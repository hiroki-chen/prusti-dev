extern crate prusti_contracts;

#[ensures="false"] //~ ERROR postcondition
fn foo1(x: bool) {}

#[ensures="false && false"] //~ ERROR postcondition
fn foo2(x: bool) {}

#[ensures="!true"] //~ ERROR postcondition
fn foo3(x: bool) {}

#[ensures="!(true || x)"] //~ ERROR postcondition
fn foo4(x: bool) {}

#[ensures="!(false || true)"] //~ ERROR postcondition
fn foo5(x: bool) {}

#[ensures="!(x || !false)"] //~ ERROR postcondition
fn foo6(x: bool) {}

#[ensures="!(x || !x)"] //~ ERROR postcondition
fn foo7(x: bool) {}

#[ensures="true ==> false"] //~ ERROR postcondition
fn foo8(x: bool) {}

#[ensures="x || true ==> !(x || !x)"] //~ ERROR postcondition
fn foo9(x: bool) {}

#[ensures="x == x"]
#[ensures="false"] //~ ERROR postcondition
fn foo10(x: bool) {}

#[ensures="false"] //~ ERROR postcondition
#[ensures="x == x"]
fn foo11(x: bool) {}

#[ensures="x == x"]
#[ensures="!true"] //~ ERROR postcondition
#[ensures="x == x"]
fn foo12(x: bool) {}

#[ensures="false"] //~ ERROR postcondition
#[ensures="result == x"]
pub fn foo13(x: u32) -> u32 {
    x
}

fn main() {}
