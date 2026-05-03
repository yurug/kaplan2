(** * Module: KTDeque.RBR.Pointer -- pointer (chain-of-packets) representation.

    Manual §4.2 / KT99 §3 / VWGP §2.2.  In the pointer representation a
    number is a list of packets, each beginning with a head digit (Green3 or
    Red3, plus the very first digit which can be Yellow3) and followed by a
    body of yellow digits.  This grouping lets [succ] skip past long yellow
    runs in O(1).

    For the Step-1 vertical slice we only need:
    - the type of packets/chains,
    - the round-trip [chain_to_number] / [number_to_chain].

    The constant-time properties of the pointer representation are not yet
    proved (deferred); the abstract [succ] in [Succ.v] operates on the
    flat [number] type and is correct independently.

    Cross-references:
    - kb/spec/data-model.md#2.2
*)

From KTDeque.Common Require Import Prelude.
From KTDeque.RBR Require Import Model.

(** A packet is a head digit followed by zero or more [Yellow3] body digits. *)
Record packet : Type := mkPacket {
  head : Digit3;
  body : list unit          (* one [tt] per yellow body digit *)
}.

(** A chain is a list of packets. *)
Definition chain : Type := list packet.

(** Round-trips: convert chain to flat digit list and back.  These are the
    only properties of the pointer representation we need at this stage. *)

Definition packet_to_digits (p : packet) : list Digit3 :=
  head p :: map (fun _ => Yellow3) (body p).

Fixpoint chain_to_number (c : chain) : number :=
  match c with
  | [] => []
  | p :: rest => packet_to_digits p ++ chain_to_number rest
  end.

(** [number_to_chain] is total but heuristic for now.  Each non-yellow
    digit starts a new packet; trailing yellows attach to it. *)

Fixpoint group_yellows (n : number) : packet * number :=
  match n with
  | Yellow3 :: rest =>
      let '(p, tail) := group_yellows rest in
      ({| head := head p; body := tt :: body p |}, tail)
  | _ => ({| head := Green3; body := [] |}, n)
  end.

(** Top-level packetizer: read until non-yellow, then start a new packet. *)
Fixpoint number_to_chain_aux (fuel : nat) (n : number) : chain :=
  match fuel, n with
  | 0, _ => []
  | _, [] => []
  | S k, d :: rest =>
      match d with
      | Yellow3 =>
          (* leading yellow *)
          let '(p, tail) := group_yellows rest in
          {| head := Yellow3; body := body p |} :: number_to_chain_aux k tail
      | _ =>
          let '(p, tail) := group_yellows rest in
          {| head := d; body := body p |} :: number_to_chain_aux k tail
      end
  end.

Definition number_to_chain (n : number) : chain :=
  number_to_chain_aux (S (length n)) n.

(** Sanity: empty chain corresponds to empty number. *)
Lemma chain_to_number_nil : chain_to_number [] = [].
Proof. reflexivity. Qed.

(** ** Stub for the constant-time property.

    The pointer representation enables O(1) [succ] in the abstract sense:
    only the first packet's head needs to change.  We do NOT prove this here;
    the proof would be cleaner once Section 4 / Section 6 lift the same
    pattern.  See manual §4.2 for the full story. *)
