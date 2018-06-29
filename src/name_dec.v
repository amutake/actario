Set Implicit Arguments.
Unset Strict Implicit.

Require Import ssreflect mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat.
Require Import syntax.

Lemma name_not_cycle : forall n g, n <> (generated g n).
Proof.
  elim.
  - move=> m g contra.
    inversion contra.
  - move=> g n IH g'.
    case=> geq neq.
    move: IH => /(_ g).
      by apply.
Qed.

Lemma name_neg_cycle : forall (n : name) g, n != generated g n.
Proof.
  move=> n g.
  eapply introN.
  apply: eqP.
  apply: name_not_cycle.
Qed.

Lemma name_not_cycle2 : forall n g1 g2, n <> (generated g2 (generated g1 n)).
Proof.
  elim.
  - move=> m g1 g2 contra.
    inversion contra.
  - move=> g n IH g1 g2.
    case=> geq neq.
    move: IH => /(_ g g1); by apply.
Qed.

Lemma name_dec : forall n1 n2 : name, { n1 = n2 } + { n1 <> n2 }.
Proof.
  move=> n1 n2.
  eapply decP.
  apply eqP.
Qed.

Lemma name_eq_true : forall n : name, n == n = true.
Proof.
  exact: eq_refl.
Qed.
