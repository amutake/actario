Set Implicit Arguments.
Unset Strict Implicit.

Require Import ssreflect mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat.
Require Import Coq.Program.Equality Coq.Bool.Bool Coq.Sorting.Permutation.
Require Import util syntax semantics name_dec.

(* 自分の親も必ず入っている (全部つながっている) *)
(* chain という名前微妙？ *)
Definition chain' (actors : seq actor) :=
  all (fun n =>
         if n is generated _ p then
           p \in (map actor_name actors)
         else true)
      (map actor_name actors).

Definition chain (c : config) :=
  forall n p, generated n p \in map actor_name c ->
              p \in map actor_name c.

Lemma perm_chain :
  forall s s',
    Permutation s s' ->
    chain s ->
    chain s'.
Proof.
  move=> s s' perm H.
  rewrite/chain.
  move=> n p.
  move/(_ _ _ _ perm): Permutation_sym=> perm'.
  move/(perm_map_in perm')=> H'.
  apply/(perm_map_in perm).
  move: H; rewrite/chain'.
  by move/(_ n p H').
Qed.

Lemma new_trans_chain :
  forall c c' child,
    chain c ->
    c ~(New child)~> c' ->
    chain c'.
Proof.
  move=> c c' child ch tr.
  inversion tr; subst; clear tr.
  apply (perm_chain (Permutation_sym H1)).
  move/(perm_chain H0): ch.
  rewrite/chain/=.
  move=> chH n p.
  repeat rewrite in_cons.
  case/or3P.
  - move/eqP=> H; inversion H; subst.
    apply/or3P; constructor 2; done.
  - move/eqP=> H; move/(_ n p): chH; rewrite -H.
    (repeat rewrite in_cons)=> chH.
    apply/or3P; constructor 3.
    have chH_cond : (generated n p == generated n p) || (generated n p \in [seq actor_name i | i <- rest]) by apply/orP; left.
    move/(_ chH_cond): chH.
    case/orP; last done.
    move/eqP=> contra; exfalso; apply/(name_not_cycle contra).
  - move=> H; move/(_ n p): chH.
    (repeat rewrite in_cons).
    have chH_cond : (generated n p == parent) || (generated n p \in [seq actor_name i | i <- rest]) by apply/orP; right.
    move/(_ chH_cond).
    case/orP.
    + move/eqP=> ->.
      by apply/or3P; constructor 2.
    + move=> ans; by apply/or3P; constructor 3.
Qed.

(* lemmas below are for new_trans_gen_fresh *)

Lemma chain_no_parent_no_child :
  forall c parent_name,
    chain c ->
    parent_name \notin (map actor_name c) ->
    forall g,
      generated g parent_name \notin (map actor_name c).
Proof.
  move=> c parent_name ch no_parent g.
  move: ch; rewrite/chain.
  move/(_ g parent_name)=> ch.
  apply/negP; move/ch.
  by apply/negP.
Qed.

Lemma chain_decided_by_only_name :
  forall c c',
    Permutation (map actor_name c) (map actor_name c') ->
    chain c ->
    chain c'.
Proof.
  move=> c c' perm.
  rewrite/chain=> ch n p gen_in.
  apply/(perm_in perm)/(ch n p).
  by apply/(perm_in (Permutation_sym perm)).
Qed.
