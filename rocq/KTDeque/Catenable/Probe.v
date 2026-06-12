From Stdlib Require Import List Arith Bool.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops BufPrims OpsFast
  OpsFused FlatChain FlatOps.

Set Implicit Arguments.

Lemma probe : forall A (k : kind) (p s : buffer (fstored A)) rest,
    pop_raw_f (fc_er (FFlat k p s rest))
    = option_map (fun '(x, c') => (fs_er x, fc_er c'))
        (pop_raw_x (FFlat k p s rest)).
Proof.
  intros A k p s rest.
  rewrite fc_er_flat. cbn [pop_raw_f pop_raw_x root_and_child].
  match goal with |- ?G => idtac "GOAL1:" G end.
Abort.
