(** * Module: KTDeque.Extract.Extraction -- OCaml extraction.

    Extract the abstract packet-chain deque and its operations to OCaml.
    This produces a runnable, persistent, purely-functional Section-4
    deque suitable for benchmarking against Viennot's deque4. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From KTDeque.Common Require Import Element Buf5 Buf5Ops.
From KTDeque.DequePtr Require Import Model OpsAbstract OpsKT.

Set Extraction Output Directory "kt_extracted".

(** Extract Coq types to OCaml's native types where possible. *)
Extraction Language OCaml.

Extraction "kt_deque_ptr.ml"
  ElementTree.t
  ElementTree.to_list
  ElementTree.level
  ElementTree.base
  ElementTree.pair
  ElementTree.unpair
  KTDeque.Common.Buf5.Buf5
  buf5_size
  buf5_seq
  KTDeque.DequePtr.Model.Chain
  KTDeque.DequePtr.Model.Packet
  chain_to_list
  empty_chain
  buf5_push_naive
  buf5_pop_naive
  buf5_inject_naive
  buf5_eject_naive
  push_chain
  pop_chain
  inject_chain
  eject_chain
  push_chain_full
  inject_chain_full
  pop_chain_full
  eject_chain_full
  push_chain_rec
  inject_chain_rec
  pop_chain_rec
  eject_chain_rec
  push_kt
  inject_kt
  pop_kt
  eject_kt
  empty_kchain
  push_kt2
  inject_kt2
  pop_kt2
  eject_kt2
  push_kt3
  inject_kt3
  pop_kt3
  eject_kt3
  push_kt4
  inject_kt4
  pop_kt4
  eject_kt4
  kchain_to_list.
