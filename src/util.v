Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.

Section Seq.

  Variable A : Type.
  Variable E : eqType.

  Lemma inP : forall (e : E) (s : seq E), reflect (In e s) (e \in s).
  Proof.
    move=> e; elim=> /=; first by constructor.
    move=> a l IH.
    rewrite in_cons.
    apply/iffP.
    - apply ((e == a) \/ (e \in l)).
    - apply/orP.
    - case.
      + by move/eqP; left.
      + by move/IH; right.
    - case.
      + by move=> ->; left.
      + by move/IH; right.
  Qed.

  Lemma map_compatible :
    forall (T1 T2 : Type) (f : T1 -> T2) s,
      List.map f s = map f s.
  Proof. by []. Qed.

  Lemma perm_map :
    forall (A B : Type) (s s' : seq A) (f : A -> B),
      Permutation s s' ->
      Permutation (map f s) (map f s').
  Proof.
    move=> A0 B0 s s' f.
    rewrite -map_compatible.
    rewrite -map_compatible.
    apply Permutation_map.
  Qed.

  Lemma perm_in :
    forall (s s' : seq E) (e : E),
      Permutation s s' ->
      e \in s ->
      e \in s'.
  Proof.
    move=> s s' e.
    move/(Permutation_in e)=> H.
    by move/inP/H/inP.
  Qed.

  Lemma perm_in_eq :
    forall (s s' : seq E) (e : E),
      Permutation s s' ->
      (e \in s) = (e \in s').
  Proof.
    move=> s s' e perm.
    apply/idP/idP.
    - by apply perm_in.
    - apply/perm_in.
      by apply Permutation_sym.
  Qed.

  Lemma perm_map_in :
    forall (s s' : seq A) (f : A -> E) (e : E),
      Permutation s s' ->
      e \in [seq f i | i <- s] ->
      e \in [seq f i | i <- s'].
  Proof.
    move=> s s' f e.
    move/perm_map; move/(_ E f).
    apply perm_in.
  Qed.

  Lemma perm_map_in_eq :
    forall (s s' : seq A) (f : A -> E) (e : E),
      Permutation s s' ->
      (e \in [seq f i | i <- s]) = (e \in [seq f i | i <- s']).
  Proof.
    move=> s s' f e perm.
    apply/idP/idP.
    - by apply perm_map_in.
    - apply perm_map_in.
      by apply Permutation_sym.
  Qed.

  Lemma perm_all :
    forall (A : Type) (s s' : seq A) (p : A -> bool),
      Permutation s s' ->
      all p s ->
      all p s'.
  Proof.
    move=> A0 s s' p; elim.
    - done.
    - move=> x l l' perm IH /=.
      case/andP=> ? ?; apply/andP; split; [ done | by apply IH ].
    - move=> x y l /=.
      by case/and3P=> ? ? ?; apply/and3P; constructor.
    - move=> l l' l'' perm IH perm' IH'.
      by move/IH/IH'.
  Qed.

  Lemma perm_all_eq :
    forall (A : Type) (s s' : seq A) (p : A -> bool),
      Permutation s s' ->
      all p s = all p s'.
  Proof.
    move=> A0 s s' p perm.
    apply/idP/idP.
    - by apply perm_all.
    - apply perm_all.
      by apply Permutation_sym.
  Qed.

  Lemma perm_map_all :
    forall (A B : Type) (s s' : seq A) (f : A -> B) (p : B -> bool),
      Permutation s s' ->
      all p [seq f i | i <- s] ->
      all p [seq f i | i <- s'].
  Proof.
    move=> A0 B0 s s' f p.
    move/perm_map; move/(_ B0 f).
    apply perm_all.
  Qed.

  Lemma perm_map_all_eq :
    forall (A B : Type) (s s' : seq A) (f : A -> B) (p : B -> bool),
      Permutation s s' ->
      all p [seq f i | i <- s] = all p [seq f i | i <- s'].
  Proof.
    move=> A0 B0 s s' f p perm.
    apply/idP/idP.
    - by apply perm_map_all.
    - apply perm_map_all.
      by apply Permutation_sym.
  Qed.

  Lemma perm_uniq :
    forall (s s' : seq E),
      Permutation s s' ->
      uniq s ->
      uniq s'.
  Proof.
    move=> s s'; elim.
    - done.
    - move=> x l l' perm IH.
      repeat rewrite cons_uniq.
      case/andP=> x_notin u; apply/andP; split; last by apply/IH.
      apply/negP; move/(perm_in (Permutation_sym perm)).
      by apply/negP.
    - move=> x y l.
      repeat rewrite cons_uniq.
      repeat rewrite in_cons.
      case/and3P=> xy_yl xl u.
      apply/and3P; split; last done.
      + apply/negP.
        case/orP; [ move/eqP | by apply/negP ].
        move=> xy.
        move/negP: xy_yl; apply.
        apply/orP; left; rewrite xy; done.
      + apply/negP=> yl.
        move/negP: xy_yl; apply.
        by apply/orP; right.
    - auto.
  Qed.

  Lemma perm_map_uniq :
    forall (s s' : seq A) (f : A -> E),
      Permutation s s' ->
      uniq (map f s) ->
      uniq (map f s').
  Proof.
    move=> s s' f.
    move/perm_map; move/(_ _ f).
    apply perm_uniq.
  Qed.

End Seq.
