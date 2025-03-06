use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::external_body]
struct MySeq;

impl MySeq {
    spec fn empty() -> MySeq;
    spec fn len(self) -> nat;
    spec fn push(self, value: int) -> MySeq;
}

proof fn test(x: int, y: int) {
    let s = MySeq::empty();
    assert(
        s.push(x + y)
     == s.push(y + x)
    );
}

proof fn axiom_my_seq_empty()
    ensures
        // ... empty len is 0 ...,
        MySeq::empty().len() == 0,
{
    admit();
}

proof fn axiom_my_seq_push_len(s: MySeq, value: int)
    ensures
        // ... push adds 1 to len ...,
        s.push(value).len() == s.len() + 1,
{
    admit();
}

proof fn test2(x: int, y: int) {
    let s0 = MySeq::empty();
    let s1 = s0.push(x + y);
    let s2 = s1.push(x - y);
    axiom_my_seq_empty();
    // axiom_my_seq_push_len(s0, x + y);
    // axiom_my_seq_push_len(s1, x - y);
    axiom_my_seq_push_len_quant();
    assert(s2.len() == 2); // make this succeed
}

proof fn axiom_my_seq_push_len_quant()
    ensures
        forall|s: MySeq, value: int| 
        // ... push adds 1 to len ...,
        s.push(value).len() == s.len() + 1,
{
    admit();
}

proof fn test3(x: int, y: int) {
//     broadcast use axiom_my_seq_empty;
//     broadcast use axiom_my_seq_push_len;

// ...
}


} // verus!
