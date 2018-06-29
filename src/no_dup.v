Set Implicit Arguments.
Unset Strict Implicit.

Require Import ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat.
Require Import Coq.Sorting.Permutation.
Require Import util syntax semantics name_dec chain gen_fresh.

(* list actor 内のアクターについて、アクターの名前が被ってない *)
Definition no_dup (c : config) := uniq (map actor_name c).

Lemma perm_no_dup :
  forall c c',
    Permutation c c' ->
    no_dup c ->
    no_dup c'.
Proof.
  move=> c c'.
  rewrite/no_dup.
  apply/perm_map_uniq.
Qed.

Lemma new_trans_no_dup :
  forall c c' child,
    gen_fresh c ->
    no_dup c ->
    c ~(New child)~> c' ->
    no_dup c'.
Proof.
  move=> c c' child fr no tr.
  inversion tr; subst; clear tr.
  move/(perm_gen_fresh H0)/gen_fresh_head: fr=>/= child_notin.
  apply/(perm_no_dup (Permutation_sym H1)).
  move: no.
  move/(perm_no_dup H0).
  rewrite/no_dup/=.
  case/andP=> parent_notin u.
    by apply/and3P; split.
Qed.

Lemma no_dup_decided_by_only_name :
  forall c c',
    Permutation (map actor_name c) (map actor_name c') ->
    no_dup c ->
    no_dup c'.
Proof.
  move=> c c' perm.
  rewrite/no_dup=> no.
  by apply/(perm_uniq perm).
Qed.

Lemma no_dup_head :
  forall a c,
    no_dup (a :: c) ->
    actor_name a \notin [seq actor_name i | i <- c].
Proof.
  move=> a c.
  rewrite/no_dup/=.
    by case/andP=> ? _.
Qed.

Lemma name_next_in_name :
  forall c nm nx,
    (nm, nx) \in [seq name_next i | i <- c] ->
    nm \in [seq actor_name i | i <- c].
Proof.
  move=> c nm nx.
  rewrite/name_next.
  elim: c=> //.
  move=> a l H /=.
  rewrite in_cons.
  case/orP.
  - case/eqP=> ? ?; subst.
      by rewrite in_cons; apply/orP; left.
  - move/H=> ans.
    by rewrite in_cons; apply/orP; right.
Qed.

Lemma notin_cons :
  forall (E : eqType) (e x : E) l,
    e \notin (x :: l) ->
    e \notin l.
Proof.
  move=> E e x l.
  move/negP=> H.
  apply/negP=> contra.
  apply H.
  by rewrite in_cons; apply/orP; right.
Qed.

Lemma no_grandchild :
  forall a c,
    chain (a :: c) ->
    gen_fresh (a :: c) ->
    forall g,
      generated g (generated (next_num a) (actor_name a)) \notin [seq actor_name i | i <- c].
Proof.
  move=> a c ch fr g.
  move/(_ _ (generated (next_num a) (actor_name a)) ch _ g): chain_no_parent_no_child=> /= H.
  apply/notin_cons; first apply/(actor_name a).
  apply H.
  by move/(_ a c fr): gen_fresh_head=>/=; apply.
Qed.

Lemma name_next_notin :
  forall a c,
    no_dup (a :: c) ->
    forall x,
      (actor_name a, x) \notin [seq name_next i | i <- c].
Proof.
  move=> a c no x.
  apply/negP=> contra.
  move/(_ _ _ no): no_dup_head=>/=.
  by move/negP; apply; apply/(name_next_in_name contra).
Qed.

Lemma new_trans_gen_fresh' :
  forall parent_st parent_name parent_actions parent_actions' parent_next parent_behv parent_queue
         child_st child_ini child_behv
         parent parent' child rest,
    parent = {|
       state_type := parent_st;
       actor_name := parent_name;
       remaining_actions := parent_actions;
       next_num := parent_next;
       behv := parent_behv;
       queue := parent_queue |} ->
    parent' = {|
         state_type := parent_st;
         actor_name := parent_name;
         remaining_actions := parent_actions';
         next_num := parent_next.+1;
         behv := parent_behv;
         queue := parent_queue |} ->
    child = {|
         state_type := child_st;
         actor_name := generated parent_next parent_name;
         remaining_actions := become child_ini;
         next_num := 0;
         behv := child_behv;
         queue := [::] |} ->
    gen_fresh (parent :: rest) ->
    chain (parent :: rest) ->
    no_dup (parent :: rest) ->
    gen_fresh [:: child, parent' & rest].
Proof.
  move=> parent_st parent_name parent_actions parent_actions' parent_next parent_behv parent_queue
         child_st child_ini child_behv
         parent parent' child rest.
  move=> parent_eq parent'_eq child_eq.
  move=> fr ch no.
  subst.
  rewrite/gen_fresh/name_next/=.
  move=> pn px.
  repeat rewrite in_cons.
  case/or3P.
  - case/eqP=> ? ?; subst.                            (* no_grandchild *)
    move=> child_gen contra; exfalso.
    move/(_ _ _ ch fr child_gen)/negP: no_grandchild; apply.
    rewrite/next_num/=.
    by case/or3P: contra; last done;
    rewrite eq_sym; move/eqP=> contra; exfalso;
    [ apply/(name_not_cycle contra) | apply/(name_not_cycle2 contra) ].
  - case/eqP=> ? ?; subst=> child_gen.
    repeat rewrite in_cons; case/or3P; first by case/eqP=> ?; subst.
    + by rewrite eq_sym; move/eqP=> contra; exfalso; apply/(name_not_cycle contra).
    + move/gen_fresh_increase: fr; move/(_ parent_actions parent_behv parent_queue).
      move/(_ parent_name parent_next.+1); rewrite/name_next/=.
      move=> H rest_in; apply/H; apply/orP; [ by left | by right ].
  - move/name_next_notin: no; move/(_ px)=>/= p_nin p_in child_gen gen_in.
    eapply fr; rewrite/name_next/=.
    + by apply/orP; right; apply/p_in.
    + move: gen_in; case/orP; last done.
      case/eqP=> ? ?; subst; exfalso.
        by move/negP: p_nin; apply.
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
  forall c c' child,
    chain c ->
    gen_fresh c ->
    no_dup c ->
    c ~(New child)~> c' ->
    gen_fresh c'.
Proof.
  move=> c c' child ch fr no tr.
  inversion tr as [ | | parent_st parent_name parent_behv parent_cont parent_next parent_queue child_st child_behv child_ini rest ? ? perm perm' | ]; subst; clear tr.
  apply/(perm_gen_fresh (Permutation_sym perm')).
  clear perm'.
  eapply new_trans_gen_fresh'.
  - Focus 4. by apply/(perm_gen_fresh perm).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - by apply/(perm_chain perm).
  - by apply/(perm_no_dup perm).
Qed.
