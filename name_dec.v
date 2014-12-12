Require Import String.

Require Import syntax.

Lemma name_not_cycle : forall n g, n <> (generated n g).
Proof.
  intros n g H.
  induction n.
  - inversion H; subst.
  - apply IHn.
    inversion H.
    rewrite H2 in H1.
    rewrite <- H1.
    auto.
Qed.

Lemma name_not_cycle2 : forall n g1 g2, n <> (generated (generated n g1) g2).
Proof.
  induction n; intros g1 g2 H.
  - inversion H.
  - inversion H.
    apply IHn in H1.
    auto.
Qed.

Lemma name_dec : forall n1 n2 : name, { n1 = n2 } + { n1 <> n2 }.
Proof.
  induction n1; induction n2.
  - destruct (string_dec m m0).
    + left; rewrite e; auto.
    + right; intro H; apply n; injection H; auto.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - destruct (NPeano.Nat.eq_dec g g0); subst.
    + specialize (IHn1 n2).
      destruct IHn1 as [ eq | neq ]; subst.
      * left; auto.
      * right; intro H; apply neq; inversion H; auto.
    + right; intro H; apply n; inversion H; auto.
Qed.
