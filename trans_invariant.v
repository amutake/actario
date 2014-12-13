Set Implicit Arguments.
Unset Strict Implicit.

Require Import List String Relations Program.
Import ListNotations.

Require Import util syntax semantics name_dec chain gen_fresh no_dup.

Definition trans_invariant (actors : list actor) :=
  chain actors /\ gen_fresh actors /\ no_dup actors.

Definition trans_invariant_config (conf : config) :=
  match conf with
    | conf _ actors => trans_invariant actors
  end.

Hint Unfold trans_invariant trans_invariant_config.

(* ___trans_trans_invariant *)
(* dispatch, send, become はほとんど同じ (apply gen_fresh_only_name_gen のところだけ違う) なので、まとめたい *)

Lemma dispatch_trans_trans_invariant :
  forall msgs msgs' actors actors',
    trans_invariant actors ->
    trans Dispatch (conf msgs actors) (conf msgs' actors') ->
    trans_invariant actors'.
Proof.
  intros msgs msgs' actors actors' inv tr.
  inversion tr; subst.
  inversion H2; subst.
  clear tr H2.
  destruct inv as [ ch inv ]; destruct inv as [ fr no ].
  repeat split.
  - unfold chain in *.
    rewrite map_app in *.
    simpl in *.
    apply Forall_app_iff in ch; destruct ch as [ ch_l ch ];
    apply Forall_cons_iff in ch; destruct ch as [ ch_m ch_r ].
    apply Forall_app_iff; split; auto.
  - apply gen_fresh_only_name_gen with (actors_l ++ actor_state addr [] behv number :: actors_r).
    + repeat (rewrite map_app); auto.
    + auto.
  - unfold no_dup in *.
    rewrite map_app.
    simpl.
    rewrite map_app in no.
    simpl in no; auto.
Qed.

Lemma send_trans_trans_invariant :
  forall msgs msgs' actors actors',
    trans_invariant actors ->
    trans Send (conf msgs actors) (conf msgs' actors') ->
    trans_invariant actors'.
Proof.
  intros msgs msgs' actors actors' inv tr.
  inversion tr; subst.
  inversion H2; subst.
  clear tr H2.
  destruct inv as [ ch inv ]; destruct inv as [ fr no ].
  repeat split.
  - unfold chain in *.
    rewrite map_app in *.
    simpl in *.
    apply Forall_app_iff in ch; destruct ch as [ ch_l ch ];
    apply Forall_cons_iff in ch; destruct ch as [ ch_m ch_r ].
    apply Forall_app_iff; split; auto.
  - apply gen_fresh_only_name_gen with (actors_l ++ actor_state addr' (send addr content :: actions) behv number :: actors_r).
    + repeat (rewrite map_app); auto.
    + auto.
  - unfold no_dup in *.
    rewrite map_app.
    simpl.
    rewrite map_app in no.
    simpl in no; auto.
Qed.

Lemma new_trans_trans_invariant :
  forall msgs msgs' actors actors',
    trans_invariant actors ->
    trans New (conf msgs actors) (conf msgs' actors') ->
    trans_invariant actors'.
Proof.
  intros msgs msgs' actors actors' inv tr.
  destruct inv as [ ch inv ]; destruct inv as [ fr no ].
  repeat split.
  - eapply new_trans_chain in ch.
    + apply ch.
    + apply tr.
  - eapply new_trans_gen_fresh in fr; auto.
    + apply fr.
    + apply tr.
  - eapply new_trans_no_dup in no; auto.
    + apply no.
    + apply tr.
Qed.

Lemma become_trans_trans_invariant :
  forall msgs msgs' actors actors',
    trans_invariant actors ->
    trans Become (conf msgs actors) (conf msgs' actors') ->
    trans_invariant actors'.
Proof.
  intros msgs msgs' actors actors' inv tr.
  inversion tr; subst.
  inversion H2; subst.
  clear tr H2.
  destruct inv as [ ch inv ]; destruct inv as [ fr no ].
  repeat split.
  - unfold chain in *.
    rewrite map_app in *.
    simpl in *.
    apply Forall_app_iff in ch; destruct ch as [ ch_l ch ];
    apply Forall_cons_iff in ch; destruct ch as [ ch_m ch_r ].
    apply Forall_app_iff; split; auto.
  - apply gen_fresh_only_name_gen with (actors_l ++ actor_state addr (become new_beh :: actions) old_beh number :: actors_r).
    + repeat (rewrite map_app); auto.
    + auto.
  - unfold no_dup in *.
    rewrite map_app.
    simpl.
    rewrite map_app in no.
    simpl in no; auto.
Qed.

Hint Resolve
     dispatch_trans_trans_invariant
     send_trans_trans_invariant
     new_trans_trans_invariant
     become_trans_trans_invariant.

Theorem trans_trans_invariant :
  forall typ msgs msgs' actors actors',
    trans_invariant actors ->
    trans typ (conf msgs actors) (conf msgs' actors') ->
    trans_invariant actors'.
Proof.
  intros typ msgs msgs' actors actors' inv tr.
  destruct typ.
  - apply dispatch_trans_trans_invariant in tr; auto.
  - apply send_trans_trans_invariant in tr; auto.
  - apply new_trans_trans_invariant in tr; auto.
  - apply become_trans_trans_invariant in tr; auto.
Qed.

Hint Resolve trans_trans_invariant.

(* trans_star *)

Theorem trans_star_trans_invariant :
  forall conf conf',
    trans_invariant_config conf ->
    trans_star conf conf' ->
    trans_invariant_config conf'.
Proof.
  intros conf conf' conf_inv star.
  induction star; auto.
  apply IHstar.
  unfold trans_invariant_config in conf_inv.
  destruct c1 as [ msgs1 as1 ].
  destruct c2 as [ msgs2 as2 ].
  eapply trans_trans_invariant in conf_inv.
  - apply conf_inv.
  - specialize (H Send).        (* <- ??? *)
    apply H.
Qed.

Lemma initial_trans_invariant :
  forall conf,
    initial_config conf ->
    trans_invariant_config conf.
Proof.
  intros conf H.
  inversion H; subst.
  clear H.
  unfold trans_invariant_config.
  unfold trans_invariant.
  repeat split.
  - unfold chain.
    apply Forall_cons_iff.
    split; simpl; auto.
  - constructor; auto.
  - unfold no_dup.
    simpl.
    auto.
Qed.

Hint Resolve initial_trans_invariant.

Theorem initial_trans_star_trans_invariant :
  forall conf conf',
    initial_config conf ->
    trans_star conf conf' ->
    trans_invariant_config conf'.
Proof.
  intros conf conf' ini star.
  apply initial_trans_invariant in ini.
  apply (trans_star_trans_invariant ini star).
Qed.

(* 初期状態から任意の遷移を任意回行っても名前は重複しない *)
Theorem initial_trans_star_no_dup :
  forall config msgs actors,
    initial_config config ->
    trans_star config (conf msgs actors) ->
    no_dup actors.
Proof.
  intros config msgs actors ini star.
  assert (trans_invariant_config (conf msgs actors)).
  - apply initial_trans_star_trans_invariant with (conf := config) (conf' := (conf msgs actors)); auto.
  - unfold trans_invariant_config in H.
    unfold trans_invariant in H.
    destruct H as [ ch H ].
    destruct H as [ fr no ].
    auto.
Qed.
