Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq mathcomp.ssreflect.ssrnat.
Require Import Coq.Sorting.Permutation.
Require Import util syntax semantics name_dec chain gen_fresh no_dup.

Definition trans_invariant (c : config) :=
  [/\ chain c, gen_fresh c & no_dup c].

Hint Unfold trans_invariant.

Lemma perm_trans_invariant :
  forall c c',
    Permutation c c' ->
    trans_invariant c ->
    trans_invariant c'.
Proof.
  move=> c c' perm.
  case;
    move/(perm_chain perm)=> ch;
    move/(perm_gen_fresh perm)=> fr;
    move/(perm_no_dup perm)=> no.
    by split.
Qed.

Lemma trans_invariant_decided_by_only_name_next :
  forall c c',
    Permutation (seq.map name_next c) (seq.map name_next c') ->
    trans_invariant c ->
    trans_invariant c'.
Proof.
  move=> c c' perm inv.
  case: inv=> ch fr no.
  split.
  - by move/perm_name_next_to_name/chain_decided_by_only_name: perm; apply.
  - by move/gen_fresh_decided_by_only_name_next: perm; apply.
  - by move/perm_name_next_to_name/no_dup_decided_by_only_name: perm; apply.
Qed.

Notation not_new l := (if l is New _ then false else true).

Lemma not_new_trans_not_modify_name_next :
  forall c c' l,
    not_new l ->
    c ~(l)~> c' ->
    Permutation (seq.map name_next c) (seq.map name_next c').
Proof.
  move=> c c' l.
  case: l => [ t m | f t m | // | m ];
    move=> _ tr;
    inversion tr as [ ? ? ? ? ? ? ? ? ? ? perm perm'
                    | ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? perm perm'
                    |
                    | ? ? ? ? ? ? ? ? ? perm perm']; subst;
  move/perm_map: perm'; move/(_ _ name_next)/Permutation_sym; rewrite/name_next/=;
  move/perm_map: perm; move/(_ _ name_next); rewrite/name_next/=;
  move=> a b; apply/(Permutation_trans a b).
Qed.

Lemma not_new_trans_trans_invariant :
  forall c c' l,
    not_new l ->
    trans_invariant c ->
    c ~(l)~> c' ->
    trans_invariant c'.
Proof.
  move=> c c' l.
  case eq_label : l=> [ t m | f t m | // | m ]; move=> _ inv tr;
  move/(_ c c' _ inv): trans_invariant_decided_by_only_name_next; apply;
  move/(_ c c' l): not_new_trans_not_modify_name_next;
  by rewrite eq_label; apply.
Qed.

Lemma new_trans_trans_invariant :
  forall c c' child,
    trans_invariant c ->
    c ~(New child)~> c' ->
    trans_invariant c'.
Proof.
  move=> c c' child.
  case=> ch fr no tr.
  split.
  - move: new_trans_chain.
    by move/(_ c c' child); apply.
  - move: new_trans_gen_fresh.
    by move/(_ c c' child); apply.
  - move: new_trans_no_dup.
    by move/(_ c c' child); apply.
Qed.

Theorem trans_trans_invariant :
  forall c c' l,
    trans_invariant c ->
    c ~(l)~> c' ->
    trans_invariant c'.
Proof.
  move=> c c' l.
  case nn_eq_label : (not_new l).
  - move=> inv tr.
    move/(_ c c' l): not_new_trans_trans_invariant.
      by rewrite nn_eq_label; apply.
  - move=> inv tr.
    case eq_label : l=> [ ? ? | ? ? ? | child | ? ]; rewrite eq_label in nn_eq_label; try done.
    move/(_ c c' child): new_trans_trans_invariant.
    rewrite eq_label in tr.
    by apply.
Qed.

Hint Resolve trans_trans_invariant.

(* trans_star *)

Theorem trans_star_trans_invariant :
  forall c c',
    trans_invariant c ->
    c ~>* c' ->
    trans_invariant c'.
Proof.
  move=> c c' inv star.
  move: inv.
  elim: star.
  - apply/perm_trans_invariant.
  - move=> c1 c2 c3.
    case=> l.
    move/trans_trans_invariant=> inv12 _ inv23 inv1.
    apply: inv23; apply: inv12; exact: inv1.
Qed.

Lemma initial_trans_invariant :
  forall c,
    initial_config c ->
    trans_invariant c.
Proof.
  move=> conf ini.
  elim: ini=> addr actions /=.
  split.
  - by rewrite/chain.
  - by rewrite/gen_fresh.
  - by rewrite/no_dup.
Qed.

Hint Resolve initial_trans_invariant.

Theorem initial_trans_star_trans_invariant :
  forall c c',
    initial_config c ->
    c ~>* c' ->
    trans_invariant c'.
Proof.
  move=> c c' ini star.
  move/initial_trans_invariant: ini=> inv.
  by apply: (trans_star_trans_invariant inv star).
Qed.

(* 初期状態から任意の遷移を任意回行っても名前は重複しない *)
Theorem initial_trans_star_no_dup :
  forall c c',
    initial_config c ->
    c ~>* c' ->
    no_dup c'.
Proof.
  move=> c c' ini star.
  have: trans_invariant c' by exact: (initial_trans_star_trans_invariant ini star).
  by case.
Qed.
