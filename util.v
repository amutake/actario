Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Import ListNotations.

Section Forall.

  Lemma Forall_cons_iff {A} : forall P (h : A) t,
                                Forall P (h :: t) <-> P h /\ Forall P t.
  Proof.
    intros P h t.
    split; intro H.
    - inversion H; subst.
      split; auto.
    - destruct H.
      constructor; auto.
  Qed.

  Lemma Forall_app_iff {A} : forall P (l r : list A),
                               Forall P (l ++ r) <-> Forall P l /\ Forall P r.
  Proof.
    intros P l r.
    split; intro H.
    - split.
      + induction l.
        * auto.
        * rewrite <- app_comm_cons in H.
          inversion H; subst; auto.
      + induction l; simpl in H; auto.
        inversion H; subst; auto.
    - destruct H as [ Hl Hr ].
      induction l.
      + auto.
      + simpl.
        constructor.
        * inversion Hl; subst; auto.
        * apply IHl.
          inversion Hl; subst; auto.
  Qed.

  Lemma Forall_P_eq {A} : forall (P Q : A -> Prop) l,
                            (forall a : A, P a <-> Q a) ->
                            (Forall P l <-> Forall Q l).
  Proof.
    intros P Q l H.
    split; intro F;
    apply Forall_forall;
    intros x In;
    eapply Forall_forall in F; try (apply In);
    apply H; auto.
  Qed.

  Lemma Forall_single {A} : forall P (a : A), Forall P [a] <-> P a.
  Proof.
    intros.
    split; intros H.
    inversion H; auto.
    constructor; auto.
  Qed.

  Lemma Forall_insert_iff {A} :
    forall (P : A -> Prop) xl x xr,
      Forall P (xl ++ x :: xr) <-> Forall P (x :: xl ++ xr).
  Proof.
    intros P xl x xr.
    split; intro H.
    - apply Forall_app_iff in H.
      destruct H as [ Hxl H ].
      apply Forall_cons_iff in H.
      destruct H as [ Hx Hxr ].
      apply Forall_cons_iff; split; auto.
      apply Forall_app_iff; split; auto.
    - apply Forall_cons_iff in H.
      destruct H as [ Hx H ].
      apply Forall_app_iff in H.
      destruct H as [ Hxl Hxr ].
      apply Forall_app_iff; split; auto.
  Qed.

End Forall.

Section List.

  Lemma app_cons {A} : forall (hd : A) tl, hd :: tl = [hd] ++ tl.
  Proof. auto. Qed.

  Lemma app_cons_app {A} : forall (xs : list A) y ys,
                             xs ++ y :: ys = xs ++ [y] ++ ys.
  Proof. auto. Qed.

End List.

Section NotIn.

  Lemma NotIn_cons_iff {A} : forall (a : A) hd tl,
                               ~ In a (hd :: tl) <-> a <> hd /\ ~ In a tl.
  Proof.
    intros a hd tl.
    split; intro H.
    - split; intro contra; subst.
      + apply H.
        simpl; left; auto.
      + apply H; simpl; right; auto.
    - intro contra.
      destruct H.
      simpl in contra; destruct contra as [ contra | contra ].
      + subst.
        auto.
      + easy.
  Qed.


  Lemma NotIn_app_iff {A} : forall (a : A) l r,
                              ~ In a (l ++ r) <-> ~ In a l /\ ~ In a r.
  Proof.
    intros a l r.
    split; intro H.
    - split; intro H1.
      + apply H.
        induction l.
        * inversion H1.
        * simpl in *.
          destruct H1; auto.
          right.
          apply IHl; auto.
      + apply H.
        induction l.
        * simpl; auto.
        * simpl in *.
          right; apply IHl; intro contra.
          apply H.
          right; auto.
    - intro c.
      apply in_app_iff in c.
      destruct H.
      destruct c; auto.
  Qed.

End NotIn.

Section Logic.

  Lemma forall_and_split {A} : forall (P Q : A -> Prop),
                                 (forall a, P a /\ Q a) <-> ((forall a, P a) /\ (forall a, Q a)).
  Proof.
    intros P Q.
    split; intro H.
    - split; intro a.
      + specialize (H a).
        destruct H; auto.
      + specialize (H a).
        destruct H; auto.
    - intro a.
      destruct H as [ HP HQ ]; specialize (HP a); specialize (HQ a); split; auto.
  Qed.

End Logic.

Section NoDup.

  Lemma NoDup_swap {A} :
    forall (l r : list A),
      NoDup (l ++ r) ->
      NoDup (r ++ l).
  Proof.
    intros l r; revert l; induction r; intros l H.
    - rewrite app_nil_r in H; simpl in *; auto.
    - simpl.
      constructor.
      + apply NotIn_app_iff.
        apply and_comm.
        apply NotIn_app_iff.
        apply NoDup_remove_2; auto.
      + apply IHr.
        apply NoDup_remove_1 with (a); auto.
  Qed.

  Lemma NoDup_swap_head {A} :
    forall (a b : A) t,
      NoDup (a :: b :: t) -> NoDup (b :: a :: t).
  Proof.
    induction t.
    - intro H;
      rewrite app_cons;
      apply NoDup_swap;
      simpl; auto.
    - intro H.
      assert (NoDup (a :: b :: a0 :: t)); auto.
      assert (a :: b :: a0 :: t = [a;b] ++ a0 :: t); auto.
      rewrite H1 in H0.
      apply NoDup_remove_1 in H0.
      simpl in H0.
      apply IHt in H0.
      inversion H; subst.
      inversion H5; subst.
      inversion H7; subst.
      constructor.
      + apply NotIn_cons_iff.
        split; auto.
        intro; subst.
        apply H4; auto.
        simpl; left; auto.
      + constructor.
        apply NotIn_cons_iff.
        apply NotIn_cons_iff in H4.
        destruct H4.
        apply NotIn_cons_iff in H3; destruct H3.
        split; auto.
        auto.
  Qed.

  Lemma NoDup_insert_iff {A} :
    forall l r (a : A),
      NoDup (l ++ a :: r) <-> NoDup (a :: l ++ r).
  Proof.
    induction l; intros r a'; split; intro H.
    - simpl in *; auto.
    - simpl in *; auto.
    - simpl in *.
      apply NoDup_swap_head.
      inversion H; subst.
      apply IHl in H3.
      apply NotIn_app_iff in H2.
      destruct H2 as [ Hl H2 ].
      apply NotIn_cons_iff in H2.
      destruct H2 as [ Ha Hr ].
      assert (~ In a (a' :: l ++ r)).
      + apply NotIn_cons_iff.
        split; auto.
        apply NotIn_app_iff.
        split; auto.
      + apply NoDup_cons; auto.
    - simpl in *.
      apply NoDup_swap_head in H.
      inversion H; subst.
      apply IHl in H3.
      apply NotIn_cons_iff in H2.
      destruct H2 as [ Ha H2 ].
      apply NotIn_app_iff in H2.
      destruct H2 as [ Hl Hr ].
      assert (~ In a (l ++ a' :: r)).
      + apply NotIn_app_iff.
        split; auto.
        apply NotIn_cons_iff.
        split; auto.
      + apply NoDup_cons; auto.
  Qed.

End NoDup.
