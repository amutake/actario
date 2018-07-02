Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
Require Import Coq.Sorting.Permutation.
Require Import semantics fairness specification auto.

Ltac unfold_eventually u :=
  rewrite/u/eventually_do_label/eventually_processed.

Ltac step p_is_path p :=
  move/(_ _ _ _ p_is_path p): trace_path;
  rewrite/calc_trans/=.

Ltac step_until_stop is_path p0 :=
  let P := fresh "p" in
  try (progress step is_path p0=> P; step_until_stop is_path P).

Ltac finish i p p' :=
  exists i; eexists; eexists;
         split; last split; [ apply p | apply p' | ];
         (eapply trans_receive || eapply trans_send || eapply trans_new || eapply trans_self);
         apply/Permutation_refl.
