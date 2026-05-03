//! # ktdeque-deque4
//!
//! A persistent Kaplan-Tarjan Section-4 (non-catenable) deque, hand-written
//! in Rust.
//!
//! ## v0 substrate
//!
//! The v0 implementation uses a persistent `Vec<T>` (cloned on update) as
//! the backing store.  This is correct but **not** real-time O(1) and does
//! NOT yet mirror the [`KTDeque/Deque4/HeapCells.v`] cell layout that the
//! simulation theorem (ADR-0008/0009) requires.
//!
//! v1 will replace the internals with a proper chain of cells using
//! [`std::rc::Rc`] for sharing.  See `kb/architecture/decisions/adr-0009-deque4-end-to-end.md`.
//!
//! ## Persistence
//!
//! Every operation returns a new `Deque<T>` value sharing structure with the
//! input.  The `Deque<T>` is `Clone` (cheap when `T: Clone`); operations on
//! one clone do not affect the other.
//!
//! ## API
//!
//! Mirrors the OCaml `Deque4_handwritten` module:
//! - `empty`, `is_empty`
//! - `push`, `pop`
//! - `inject`, `eject`
//! - `to_vec`

use std::rc::Rc;

/// A persistent non-catenable deque of `T`.
///
/// Operations are functional: each returns a new `Deque` sharing the
/// underlying `Rc<Vec<T>>` until divergence.
#[derive(Debug)]
pub struct Deque<T> {
    /// v0: a single shared `Vec`.  Future versions will replace with a
    /// `Chain` mirroring `KTDeque/Deque4/HeapCells.v`.
    items: Rc<Vec<T>>,
}

impl<T> Clone for Deque<T> {
    fn clone(&self) -> Self {
        Deque { items: self.items.clone() }
    }
}

impl<T: Clone> Deque<T> {
    /// The empty deque.
    pub fn empty() -> Self {
        Deque { items: Rc::new(Vec::new()) }
    }

    /// `true` iff the deque has no elements.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Number of elements in the deque (unspecified time).
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Insert `x` at the front; returns a new deque.
    ///
    /// Sequence law (P1): `to_vec(push(x, d)) == [x] ++ to_vec(d)`.
    pub fn push(&self, x: T) -> Self {
        let mut v = Vec::with_capacity(self.items.len() + 1);
        v.push(x);
        v.extend(self.items.iter().cloned());
        Deque { items: Rc::new(v) }
    }

    /// Remove and return the front element + the remaining deque.
    /// Returns `None` if empty.
    ///
    /// Sequence law (P2):
    /// - `pop(d) == None  iff  to_vec(d) == []`
    /// - `pop(d) == Some(x, d')  →  to_vec(d) == [x] ++ to_vec(d')`
    pub fn pop(&self) -> Option<(T, Self)> {
        if self.items.is_empty() {
            None
        } else {
            let x = self.items[0].clone();
            let v: Vec<T> = self.items[1..].to_vec();
            Some((x, Deque { items: Rc::new(v) }))
        }
    }

    /// Insert `x` at the back; returns a new deque.
    ///
    /// Sequence law (P3): `to_vec(inject(d, x)) == to_vec(d) ++ [x]`.
    pub fn inject(&self, x: T) -> Self {
        let mut v: Vec<T> = self.items.iter().cloned().collect();
        v.push(x);
        Deque { items: Rc::new(v) }
    }

    /// Remove and return the deque + the back element.
    /// Returns `None` if empty.
    ///
    /// Sequence law (P4):
    /// - `eject(d) == None  iff  to_vec(d) == []`
    /// - `eject(d) == Some(d', x)  →  to_vec(d) == to_vec(d') ++ [x]`
    pub fn eject(&self) -> Option<(Self, T)> {
        if self.items.is_empty() {
            None
        } else {
            let n = self.items.len();
            let x = self.items[n - 1].clone();
            let v: Vec<T> = self.items[..n - 1].to_vec();
            Some((Deque { items: Rc::new(v) }, x))
        }
    }

    /// Render to a `Vec<T>` of base elements in deque order.
    pub fn to_vec(&self) -> Vec<T> {
        self.items.iter().cloned().collect()
    }
}

#[cfg(test)]
mod basic_tests {
    use super::*;

    #[test]
    fn empty_is_empty() {
        let d: Deque<i32> = Deque::empty();
        assert!(d.is_empty());
        assert_eq!(d.to_vec(), Vec::<i32>::new());
    }

    #[test]
    fn pop_empty_is_none() {
        let d: Deque<i32> = Deque::empty();
        assert!(d.pop().is_none());
    }

    #[test]
    fn eject_empty_is_none() {
        let d: Deque<i32> = Deque::empty();
        assert!(d.eject().is_none());
    }

    #[test]
    fn push_then_pop() {
        let d: Deque<i32> = Deque::empty();
        let d = d.push(1);
        let d = d.push(2);
        let d = d.push(3);
        assert_eq!(d.to_vec(), vec![3, 2, 1]);
        let (x, d) = d.pop().unwrap();
        assert_eq!(x, 3);
        assert_eq!(d.to_vec(), vec![2, 1]);
    }

    #[test]
    fn inject_then_eject() {
        let d: Deque<i32> = Deque::empty();
        let d = d.inject(1);
        let d = d.inject(2);
        let d = d.inject(3);
        assert_eq!(d.to_vec(), vec![1, 2, 3]);
        let (d, x) = d.eject().unwrap();
        assert_eq!(x, 3);
        assert_eq!(d.to_vec(), vec![1, 2]);
    }

    #[test]
    fn persistence() {
        let d0: Deque<i32> = Deque::empty();
        let d1 = d0.push(1);
        let d2 = d1.push(2);
        // d0, d1, d2 all retain their values
        assert_eq!(d0.to_vec(), Vec::<i32>::new());
        assert_eq!(d1.to_vec(), vec![1]);
        assert_eq!(d2.to_vec(), vec![2, 1]);
    }
}
