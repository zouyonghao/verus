#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

impl<A> Set<A> {
    #[spec]
    pub fn map<F: Fn(A) -> A>(self, f: F) -> Set<A> {
        set_new(|a: A| exists(|x: A| self.contains(x) && equal(a, f(x))))
    }
}

#[proof]
fn lemma_len0_is_empty<A>(s: Set<A>) {
    requires(s.finite() && s.len() == 0);
    ensures(equal(s, set_empty()));

    if exists(|a: A| s.contains(a)) {
        // derive contradiction:
        assert(s.remove(s.choose()).len() + 1 == 0);
    }
    assert(s.ext_equal(set_empty()));
}

#[proof]
fn lemma_len_union<A>(s1: Set<A>, s2: Set<A>) {
    requires([
        s1.finite(),
        s2.finite(),
    ]);
    ensures(s1.union(s2).len() <= s1.len() + s2.len());
    decreases(s1.len());

    if s1.len() == 0 {
        lemma_len0_is_empty::<A>(s1);
        assert(s1.union(s2).ext_equal(s2));
    } else {
        let a = s1.choose();
        if s2.contains(a) {
            assert(s1.union(s2).ext_equal(s1.remove(a).union(s2)));
        } else {
            assert(s1.union(s2).remove(a).ext_equal(s1.remove(a).union(s2)));
        }
        lemma_len_union::<A>(s1.remove(a), s2);
    }
}

#[proof]
fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>) {
    requires(s1.finite());
    ensures(s1.intersect(s2).len() <= s1.len());
    decreases(s1.len());

    if s1.len() == 0 {
        lemma_len0_is_empty::<A>(s1);
        assert(s1.intersect(s2).ext_equal(s1));
    } else {
        let a = s1.choose();
        assert(s1.intersect(s2).remove(a).ext_equal(s1.remove(a).intersect(s2)));
        lemma_len_intersect::<A>(s1.remove(a), s2);
    }
}

#[proof]
fn lemma_len_difference<A>(s1: Set<A>, s2: Set<A>) {
    requires(s1.finite());
    ensures(s1.difference(s2).len() <= s1.len());
    decreases(s1.len());

    if s1.len() == 0 {
        lemma_len0_is_empty::<A>(s1);
        assert(s1.difference(s2).ext_equal(s1));
    } else {
        let a = s1.choose();
        assert(s1.difference(s2).remove(a).ext_equal(s1.remove(a).difference(s2)));
        lemma_len_difference::<A>(s1.remove(a), s2);
    }
}

#[proof]
fn lemma_len_filter<A, F: Fn(A) -> bool>(s: Set<A>, f: F) {
    requires(s.finite());
    ensures([
        s.filter(f).finite(),
        s.filter(f).len() <= s.len(),
    ]);
    decreases(s.len());

    lemma_len_intersect::<A>(s, set_new(f));
}
