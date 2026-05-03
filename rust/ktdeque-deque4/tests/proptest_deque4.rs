//! proptest-based PBT for Deque4.
//!
//! Strategy (mirrors the OCaml `test_qcheck/test_deque4.ml`): generate random
//! sequences of operations, apply to both the candidate Deque and a
//! `Vec`-based reference, and assert that `to_vec` of the candidate equals
//! the reference at every step.

use ktdeque_deque4::Deque;
use proptest::prelude::*;

#[derive(Debug, Clone)]
enum Op {
    Push(i32),
    Pop,
    Inject(i32),
    Eject,
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        (0..1000i32).prop_map(Op::Push),
        Just(Op::Pop),
        (0..1000i32).prop_map(Op::Inject),
        Just(Op::Eject),
    ]
}

fn ops_strategy() -> impl Strategy<Value = Vec<Op>> {
    proptest::collection::vec(op_strategy(), 1..100)
}

fn step_deque(d: &Deque<i32>, op: &Op) -> Deque<i32> {
    match op {
        Op::Push(x) => d.push(*x),
        Op::Pop => match d.pop() {
            Some((_, d2)) => d2,
            None => d.clone(),
        },
        Op::Inject(x) => d.inject(*x),
        Op::Eject => match d.eject() {
            Some((d2, _)) => d2,
            None => d.clone(),
        },
    }
}

fn step_ref(r: &mut Vec<i32>, op: &Op) {
    match op {
        Op::Push(x) => r.insert(0, *x),
        Op::Pop => {
            if !r.is_empty() {
                r.remove(0);
            }
        }
        Op::Inject(x) => r.push(*x),
        Op::Eject => {
            r.pop();
        }
    }
}

proptest! {
    /// P_obs: to_vec of candidate equals the reference at every step.
    #[test]
    fn to_vec_matches_reference(ops in ops_strategy()) {
        let mut d: Deque<i32> = Deque::empty();
        let mut r: Vec<i32> = Vec::new();
        prop_assert_eq!(d.to_vec(), r.clone());
        for op in &ops {
            d = step_deque(&d, op);
            step_ref(&mut r, op);
            prop_assert_eq!(d.to_vec(), r.clone());
        }
    }

    /// T21: push x then pop returns x and original.
    #[test]
    fn push_pop_id(x in 0..1000i32) {
        let d: Deque<i32> = Deque::empty();
        let d = d.push(x);
        let (y, d) = d.pop().unwrap();
        prop_assert_eq!(y, x);
        prop_assert!(d.is_empty());
    }

    /// T_inj: inject x then eject returns x and original.
    #[test]
    fn inject_eject_id(x in 0..1000i32) {
        let d: Deque<i32> = Deque::empty();
        let d = d.inject(x);
        let (d, y) = d.eject().unwrap();
        prop_assert_eq!(y, x);
        prop_assert!(d.is_empty());
    }

    /// T15: persistence — old handle still has its content.
    #[test]
    fn persistence(ops in proptest::collection::vec(op_strategy(), 1..50)) {
        let mut d: Deque<i32> = Deque::empty();
        for op in &ops {
            d = step_deque(&d, op);
        }
        let snapshot = d.to_vec();
        let _d2 = d.push(99);
        prop_assert_eq!(d.to_vec(), snapshot);
    }
}
