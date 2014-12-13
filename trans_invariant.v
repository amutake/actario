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

Lemma trans_invariant_related_only_name_number :
  forall actors actors',
    map G.ns actors = map G.ns actors' ->
    trans_invariant actors ->
    trans_invariant actors'.
Proof.
  intros actors actors' ns_eq inv.
  destruct inv as [ ch inv ].
  destruct inv as [ fr no ].
  repeat split.
  - apply nss_eq_ns in ns_eq.
    apply chain_related_only_name in ns_eq; auto.
  - apply gen_fresh_related_only_name_number in ns_eq; auto.
  - apply nss_eq_ns in ns_eq.
    apply no_dup_related_only_name in ns_eq; auto.
Qed.

Lemma not_new_trans_not_modify_name_number :
  forall tr_type msgs msgs' actors actors',
    tr_type <> New ->
    trans tr_type (conf msgs actors) (conf msgs' actors') ->
    map G.ns actors = map G.ns actors'.
Proof.
  intros tr_type msgs msgs' actors actors' neq tr.
  destruct tr_type; try (exfalso; apply neq; reflexivity); clear neq;
  inversion tr; subst;
  repeat (rewrite map_app; simpl; idtac);
  auto.
Qed.

Lemma not_new_trans_trans_invariant :
  forall tr_type msgs msgs' actors actors',
    tr_type <> New ->
    trans_invariant actors ->
    trans tr_type (conf msgs actors) (conf msgs' actors') ->
    trans_invariant actors'.
Proof.
  intros tr_type msgs msgs' actors actors' neq inv tr.
  eapply trans_invariant_related_only_name_number.
  - eapply not_new_trans_not_modify_name_number.
    + apply neq.
    + apply tr.
  - apply inv.
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

Lemma trans_type_dec : forall t1 t2 : trans_type, { t1 = t2 } + { t1 <> t2 }.
Proof.
  intros t1 t2.
  destruct t1, t2; try (left; reflexivity); try (right; intro H; easy).
Qed.

Theorem trans_trans_invariant :
  forall typ msgs msgs' actors actors',
    trans_invariant actors ->
    trans typ (conf msgs actors) (conf msgs' actors') ->
    trans_invariant actors'.
Proof.
  intros typ msgs msgs' actors actors' inv tr.
  destruct (trans_type_dec typ New).
  - subst.
    apply new_trans_trans_invariant in tr; auto.
  - apply not_new_trans_trans_invariant in tr; auto.
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
