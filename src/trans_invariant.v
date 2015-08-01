Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrnat.
Require Import util syntax semantics name_dec chain gen_fresh no_dup.

Definition trans_invariant (actors : seq actor) :=
  [/\ chain actors, gen_fresh actors & no_dup actors].

Definition trans_invariant_config (conf : config) :=
  let: _ >< actors := conf in
  trans_invariant actors.

Hint Unfold trans_invariant trans_invariant_config.

Lemma trans_invariant_decided_by_only_name_and_next_number :
  forall actors actors',
    map name_next actors = map name_next actors' ->
    trans_invariant actors ->
    trans_invariant actors'.
Proof.
  move=> actors actors' nn_eq inv.
  case: inv=> ch fr no.
  split.
  - by move/name_next_eq_name/chain_decided_by_only_name: nn_eq; apply.
  - by move/gen_fresh_decided_by_only_name_and_next_number: nn_eq; apply.
  - by move/name_next_eq_name/no_dup_decided_by_only_name: nn_eq; apply.
Qed.

Notation not_new l := (if l is New _ then false else true).

Lemma not_new_trans_not_modify_name_number :
  forall label msgs msgs' actors actors',
    not_new label ->
    (msgs >< actors) ~(label)~> (msgs' >< actors') ->
    map name_next actors = map name_next actors'.
Proof.
  move=> label msgs msgs' actors actors'.
  case: label => [ to from content | from to content | // | me ];
    move=> _ tr;
    inversion tr; subst;
      by repeat (rewrite map_cat; simpl).                                                        Qed.

Lemma not_new_trans_trans_invariant :
  forall label msgs msgs' actors actors',
    not_new label ->
    trans_invariant actors ->
    (msgs >< actors) ~(label)~> (msgs' >< actors') ->
    trans_invariant actors'.
Proof.
  move=> label msgs msgs' actors actors'.
  case eq_label : label=> [ t f c | f t c | // | m ]; move=> _ inv tr;
    move/(_ actors actors' _ inv): trans_invariant_decided_by_only_name_and_next_number; apply;
    move/(_ label msgs msgs' actors actors'): not_new_trans_not_modify_name_number;
      by rewrite eq_label; apply.
Qed.

Lemma new_trans_trans_invariant :
  forall msgs msgs' actors actors' child,
    trans_invariant actors ->
    (msgs >< actors) ~(New child)~> (msgs' >< actors') ->
    trans_invariant actors'.
Proof.
  move=> msgs msgs' actors actors' child.
  case=> ch fr no tr.
  split.
  - move: new_trans_chain.
    by move/(_ msgs msgs' actors actors' child); apply.
  - move: new_trans_gen_fresh.
    by move/(_ msgs msgs' actors actors' child); apply.
  - move: new_trans_no_dup.
    by move/(_ msgs msgs' actors actors' child); apply.
Qed.

Theorem trans_trans_invariant :
  forall label msgs msgs' actors actors',
    trans_invariant actors ->
    (msgs >< actors) ~(label)~> (msgs' >< actors') ->
    trans_invariant actors'.
Proof.
  move=> label msgs msgs' actors actors'.
  case nn_eq_label : (not_new label).
  - move=> inv tr.
    move/(_ label msgs msgs' actors actors'): not_new_trans_trans_invariant.
      by rewrite nn_eq_label; apply.
  - move=> inv tr.
    case eq_label : label=> [ ? ? ? | ? ? ? | child | ? ]; rewrite eq_label in nn_eq_label; try done.
    move/(_ msgs msgs' actors actors' child): new_trans_trans_invariant.
    rewrite eq_label in tr.
    by apply.
Qed.

Hint Resolve trans_trans_invariant.

(* trans_star *)

Theorem trans_star_trans_invariant :
  forall conf conf',
    trans_invariant_config conf ->
    conf ~>* conf' ->
    trans_invariant_config conf'.
Proof.
  move=> conf conf' conf_inv star.
  move: conf_inv.
  elim: star; first done.
  case=> msgs1 actors1.
  case=> msgs2 actors2.
  case=> msgs3 actors3.
  rewrite/trans_invariant_config.
  case=> lbl.
  move/trans_trans_invariant=> inv12 _ inv23 inv1.
  apply: inv23; apply: inv12; exact: inv1.
Qed.

Lemma initial_trans_invariant :
  forall conf,
    initial_config conf ->
    trans_invariant_config conf.
Proof.
  move=> conf ini.
  elim: ini=> addr actions /=.
  split.
  - by rewrite/chain.
  - by constructor.
  - by rewrite/no_dup.
Qed.

Hint Resolve initial_trans_invariant.

Theorem initial_trans_star_trans_invariant :
  forall conf conf',
    initial_config conf ->
    conf ~>* conf' ->
    trans_invariant_config conf'.
Proof.
  move=> conf conf' ini star.
  move/initial_trans_invariant: ini=> inv.
  by apply: (trans_star_trans_invariant inv star).
Qed.

(* 初期状態から任意の遷移を任意回行っても名前は重複しない *)
Theorem initial_trans_star_no_dup :
  forall config msgs actors,
    initial_config config ->
    config ~>* (msgs >< actors) ->
    no_dup actors.
Proof.
  move=> config msgs actors ini star.
  have: trans_invariant_config (msgs >< actors) by exact: (initial_trans_star_trans_invariant ini star).
  by case.
Qed.
