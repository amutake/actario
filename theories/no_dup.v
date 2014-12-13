Set Implicit Arguments.
Unset Strict Implicit.

Require Import List String.
Import ListNotations.

Require Import util syntax semantics name_dec chain gen_fresh.

(* list actor 内のアクターについて、アクターの名前が被ってない *)
Definition no_dup (actors : list actor) : Prop := NoDup (map G.n actors).

Hint Constructors NoDup.

Lemma no_dup_related_only_name :
  forall actors actors',
    map G.n actors = map G.n actors' ->
    no_dup actors ->
    no_dup actors'.
Proof.
  unfold no_dup.
  intros actors actors' name_eq no.
  rewrite <- name_eq; auto.
Qed.

(* 仮定が gen_fresh だけだと成り立たない。
 * [ (((A, 0), 0) * 0) ; (A * 0) ] は gen_fresh だけど、
 * (A * 0) がアクターを生成して、
 *   [ (((A, 0), 0) * 0) ; ((A, 0) * 0) ; (A * 0) ] になったら gen_fresh ではなくなる
 *
 * 自分の親は必ずいる という条件 (chain) があれば大丈夫？
 * => no_dup も必要。同じ名前のがあると、現在の生成番号が小さい方をどんどん生成していったらいつかぶつかる。
 *)
Lemma new_trans_gen_fresh :
  forall msgs msgs' actors actors',
    chain actors ->
    gen_fresh actors ->
    no_dup actors ->
    trans New (conf msgs actors) (conf msgs' actors') ->
    gen_fresh actors'.
Proof.
  intros msgs msgs' actors actors' ch fr no tr.
  (* assert (ch' : chain actors'); *)
  (* apply new_trans_chain with (msgs := msgs) (msgs' := msgs') (actors' := actors') in ch; auto. *)
  inversion tr; subst.
  clear tr.
  constructor.
  (* 1. gen_fresh の補題「gen_number が増えても、gen_fresh は成り立つ」(gen_fresh_increase) を使う *)
  (* 2. chain の補題「子がいないなら孫もいない」(no_child_no_grandchild) もしくは「いないやつの子はいない」(no_actor_no_child) を使う??? *)
  (* 3. no_dup の条件を使う *)
  - apply gen_fresh_increase in fr.
    eapply gen_fresh_related_only_name_number with (actors := actors_l ++ actor_state addr (new behv cont) queue (S number) :: actors_r); auto.
    repeat (rewrite map_app); auto.
  - intros yet le.
    rewrite map_app.
    simpl.

    apply chain_insert_iff in ch.
    apply gen_fresh_insert_iff in fr.
    inversion fr; subst.

    assert (number <= number); auto.
    apply H5 in H.
    eapply head_leaf_child_not_in in ch.
    + simpl in ch.
      rewrite map_app in ch.
      apply NotIn_app_iff in ch.
      destruct ch as [ ch_l ch_r ].
      apply NotIn_app_iff.
      split.
      * apply ch_l.
      * apply NotIn_cons_iff.
        split; [ intro c; symmetry in c; apply name_not_cycle2 in c; auto | ].
        apply ch_r.
    + simpl; auto.
  - apply Forall_app_iff.
    unfold no_dup in no.
    rewrite map_app in no.
    simpl in no.
    apply NoDup_insert_iff in no.
    inversion no; subst.
    split.
    + apply Forall_forall.
      intros x inx.
      destruct x.
      intro peq.
      subst.
      apply NotIn_app_iff in H1.
      destruct H1 as [ H1l H1r ].
      assert (forall a actors, In a actors -> In (G.n a) (map G.n actors)).
      * induction actors; auto.
        simpl.
        intro H.
        destruct H; [ left; subst; auto | right; apply IHactors; auto ].
      * apply H in inx.
        simpl in inx.
        exfalso; auto.
    + apply Forall_cons_iff.
      split; auto.
      apply Forall_forall.
      intros x inx.
      destruct x.
      intro peq.
      subst.
      apply NotIn_app_iff in H1.
      destruct H1 as [ H1l H1r ].
      assert (forall a actors, In a actors -> In (G.n a) (map G.n actors)).
      * induction actors; auto.
        simpl.
        intro H.
        destruct H; [ left; subst; auto | right; apply IHactors; auto ].
      * apply H in inx.
        simpl in inx.
        exfalso; auto.
Qed.

Lemma new_trans_no_dup :
  forall msgs msgs' actors actors',
    gen_fresh actors ->
    no_dup actors ->
    trans New (conf msgs actors) (conf msgs' actors') ->
    no_dup actors'.
Proof.
  intros msgs msgs' actors actors' fr no tr.
  inversion tr; subst.
  eapply new_trans_fresh with (actor0 := actor_state (generated addr number) (become behv) [] 0) in fr.
  - unfold no_dup.
    simpl.
    constructor.
    + apply fr.
    + unfold no_dup in no.
      rewrite map_app in *.
      simpl in *.
      auto.
  - apply tr.
Qed.
