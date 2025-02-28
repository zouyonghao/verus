#![allow(unused_imports)]

// ANCHOR: full
use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::{pervasive::*, *};

verus! {

tokenized_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,

            #[sharding(variable)]
            pub pending_a: bool,

            #[sharding(variable)]
            pub pending_b: bool,
        }

        // ANCHOR: inv
        #[invariant]
        pub fn main_inv(&self) -> bool {
            // self.counter == (if self.inc_a { 2 as int } else { 0 }) + (if self.inc_b { 2 as int } else { 0 })
            self.counter ==
                (if self.inc_a { 2 as int } else {
                    if self.pending_a { 1 as int } else { 0 }
                }) +
                (if self.inc_b { 2 as int } else {
                    if self.pending_b { 1 as int } else { 0 }
                })
        }
        // ANCHOR_END: inv

        init!{
            initialize() {
                init counter = 0;
                init inc_a = false;
                init inc_b = false;
                init pending_a = false;
                init pending_b = false;
            }
        }

        transition!{
            tr_inc_a() {
                require(!pre.inc_a);
                require(pre.pending_a);
                update counter = pre.counter + 1;
                update inc_a = true;
            }
        }

        transition!{
            tr_inc_b() {
                require(!pre.inc_b);
                require(pre.pending_b);
                update counter = pre.counter + 1;
                update inc_b = true;
            }
        }

        transition!{
            tr_pending_a() {
                require(!pre.inc_a);
                require(!pre.pending_a);
                update counter = pre.counter + 1;
                update pending_a = true;
            }
        }

        transition!{
            tr_pending_b() {
                require(!pre.inc_b);
                require(!pre.pending_b);
                update counter = pre.counter + 1;
                update pending_b = true;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.counter < 0xffff_ffff;
            }
        }

        property!{
            finalize() {
                require(pre.inc_a);
                require(pre.inc_b);
                assert pre.counter == 4;
            }
        }

        // ANCHOR: inv_proof
        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(pre: Self, post: Self) {

        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(pre: Self, post: Self) {

        }

        #[inductive(tr_pending_a)]
        fn tr_pending_a_preserves(pre: Self, post: Self) {
            assert(pre.inc_a == post.inc_a);
            assert(pre.inc_b == post.inc_b);
            assert(pre.inc_a == false);
        }

        #[inductive(tr_pending_b)]
        fn tr_pending_b_preserves(pre: Self, post: Self) {

        }

        #[inductive(initialize)]
        fn initialize_inv(post: Self) {
            // assert(0 <= post.counter < 0xffff_ffff);
        }
        // ANCHOR_END: inv_proof
    }
);

// ANCHOR: global_struct
struct_with_invariants!{
    pub struct Global {
        // An AtomicU32 that matches with the `counter` field of the ghost protocol.
        pub atomic: AtomicU32<_, X::counter, _>,

        // The instance of the protocol that the `counter` is part of.
        pub instance: Tracked<X::Instance>,
    }

    spec fn wf(&self) -> bool {
        // Specify the invariant that should hold on the AtomicU32<X::counter>.
        // Specifically the ghost token (`g`) should have
        // the same value as the atomic (`v`).
        // Furthermore, the ghost token should have the appropriate `instance`.
        invariant on atomic with (instance) is (v: u32, g: X::counter) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }
    }
}
// ANCHOR_END: global_struct


fn main() {
    // Initialize protocol
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(inc_a_token),
        Tracked(inc_b_token),
        Tracked(pending_a_token),
        Tracked(pending_b_token),
    ) = X::Instance::initialize();
    // Initialize the counter
    let tr_instance: Tracked<X::Instance> = Tracked(instance.clone());
    let atomic = AtomicU32::new(Ghost(tr_instance), 0, Tracked(counter_token));
    let global = Global { atomic, instance: Tracked(instance.clone()) };
    let global_arc = Arc::new(global);

    // Spawn threads

    // Thread 1
    let global_arc1 = global_arc.clone();
    let join_handle1 = spawn(
        (move || -> (new_token: Tracked<X::inc_a>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                // `inc_a_token` is moved into the closure
                let tracked mut token = inc_a_token;
                let tracked mut pending_token = pending_a_token;
                let globals = &*global_arc1;
                let _ =
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&c);
                            // globals.instance.borrow().tr_inc_a(&mut c, &mut token); // atomic increment
                            globals.instance.borrow().tr_pending_a(&mut c, &mut token, &mut pending_token); // atomic increment
                        }
                    );
                let _ =
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&c);
                            globals.instance.borrow().tr_inc_a(&mut c, &mut token, &mut pending_token); // atomic increment
                        }
                    );
                Tracked(token)
            }),
    );

    // Thread 2
    let global_arc2 = global_arc.clone();
    let join_handle2 = spawn(
        (move || -> (new_token: Tracked<X::inc_b>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                // `inc_b_token` is moved into the closure
                let tracked mut token = inc_b_token;
                let tracked mut pending_token = pending_b_token;
                let globals = &*global_arc2;
                let _ =
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&mut c);
                            // globals.instance.borrow().tr_inc_b(&mut c, &mut token); // atomic increment
                            globals.instance.borrow().tr_pending_b(&mut c, &mut token, &mut pending_token); // atomic increment
                        }
                    );
                let _ =
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&c);
                            globals.instance.borrow().tr_inc_b(&mut c, &mut token, &mut pending_token); // atomic increment
                        }
                    );
                Tracked(token)
            }),
    );

    // Join threads
    let tracked inc_a_token;
    match join_handle1.join() {
        Result::Ok(token) => {
            proof {
                inc_a_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };
    let tracked inc_b_token;
    match join_handle2.join() {
        Result::Ok(token) => {
            proof {
                inc_b_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };

    // Join threads, load the atomic again
    let global = &*global_arc;
    let x =
        atomic_with_ghost!(&global.atomic => load();
        ghost c => {
            instance.finalize(&c, &inc_a_token, &inc_b_token);
        }
    );

    assert(x == 4);
}

} // verus!
  // ANCHOR_END: full
