Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Coq.Program.Equality Coq.Bool.Bool.
Require Import util syntax semantics name_dec.

(* 自分の親も必ず入っている (全部つながっている) *)
(* chain という名前微妙？ *)
Definition chain (actors : seq actor) :=
  all (fun n =>
         if n is generated _ p then
           p \in (map actor_name actors)
         else true)
      (map actor_name actors).

Lemma new_trans_parent_exists :
  forall flights flights' actors actors' child,
    child \in map actor_name actors' ->
    (flights >< actors) ~(New child)~> (flights' >< actors') ->
    if child is generated _ p then
      p \in (map actor_name actors')
    else false. (* new_actor の名前が toplevel になることはありえないので大丈夫 *)
Proof.
  move=> flights flights' actors actors'.
  case.
  - move=> m H tr.
    inversion tr.
  - move=> g n H tr.
    inversion tr; subst; clear tr.
    move=> /=; rewrite map_cat => /=.
    rewrite in_cons.
    rewrite mem_cat.
    rewrite in_cons.
    rewrite eq_refl.
    simpl.
    rewrite orb_true_r.
    rewrite orb_true_r.
    done.
Qed.

Lemma new_trans_parent_exists' :
  forall sendings sendings' actors actors' new_actor child,
    actor_name new_actor = child ->
    sendings >< actors ~(New child)~> sendings' >< (new_actor :: actors') ->
    if child is generated _ p then
      p \in (map actor_name (new_actor :: actors'))
    else false.
Proof.
  move=> sendings sendings' actors actors' new_actor child H.
  apply: new_trans_parent_exists.
  rewrite in_cons.
  move: H =>->.
  rewrite eq_refl.
  exact: orTb.
Qed.

Lemma new_trans_chain :
  forall msgs msgs' actors actors' child,
    chain actors ->
    (msgs >< actors) ~(New child)~> (msgs' >< actors') ->
    chain actors'.
Proof.
  move=> msgs msgs' actors actors' child ch tr.
  inversion tr; subst.
  move/new_trans_parent_exists': tr.
  rewrite/chain/=.
  have ggpeq : generated gen parent = generated gen parent by reflexivity.
  move/(_ ggpeq)=> pin_p.
  apply/andP; split; first done.
  move: ch.
  rewrite/chain/=; repeat (rewrite map_cat /=).
  rewrite 2!all_cat /=.
  move/and3P.
  case=> ch_l ch_p ch_r.
  apply/and3P.
  split.
  - apply/allP=> x xin.
    move/allP/(_ x xin): ch_l.
    move: xin; case: x; first done.
    move=> g n xin H.
    by rewrite in_cons; apply/orP; right.
  - destruct parent; first done.
    by rewrite in_cons; apply/orP; right.
  - apply/allP=> x xin.
    move/allP/(_ x xin): ch_r.
    move: xin; case: x; first done.
    move=> g n xin H.
    by rewrite in_cons; apply/orP; right.
Qed.

Lemma head_leaf_child_not_in :
  forall a actors gen gen',
    chain (a :: actors) ->
    (generated gen (actor_name a)) \notin (map actor_name actors) ->
    (generated gen' (generated gen (actor_name a))) \notin (map actor_name actors).
Proof.
  (* 孫がいたら矛盾 *)
  (* 1. actors の中に、((n(a), gen), gen') がいる *)
  (* 2. ((n(a), gen), gen') の親は (n(a), gen) *)
  (* 3. chain (a :: actors) から、forall a' \in actors, p(a') \in names(a :: actors) *)
  (* 4. 3 で a' = ((n(a), gen), gen') のとき、p(a') = (n(a), gen) = n(a) \/ (n(a), gen) \in names(as) となるが、左は成り立たないので、(n(a), gen) \in names(actors) が成り立つ *)
  (* 5. 仮定に (n(a), gen) \nin names(actors) があるので矛盾 *)
  case=> /= name actions next actors gen gen' ch notin.
  apply/negP=> gg_in; move/negP: notin; apply.
  move: ch; rewrite/chain/=; case/andP=> a_case all_p.
  have: generated gen name \in name :: map actor_name actors
    by move/allP/(_ (generated gen' (generated gen name)) gg_in): all_p.
  rewrite in_cons; move/orP; case; last done.
  move/eqP=> contra.
  symmetry in contra.
  by move: (name_not_cycle contra).
Qed.

Lemma chain_catC3_swap :
  forall a1 a2 a3,
    chain (a1 ++ a2 ++ a3) -> chain (a2 ++ a1 ++ a3).
Proof.
  move=> a1 a2 a3.
  rewrite/chain.
  repeat (rewrite (map_cat, all_cat) /=).
  case/and3P=> all_1 all_2 all_3.
  apply/and3P; split.
  - apply/allP=> n; case: n => [ ? | g n ]; first done.
    move=> nin; move/allP/(_ _ nin): all_2; rewrite 4!mem_cat.
    move/or3P; case=> H; apply/or3P; by [ apply: Or33 | apply: Or32 | apply: Or31 ].
  - apply/allP=> n; case: n => [ ? | g n]; first done.
    move=> nin; move/allP/(_ _ nin): all_1; rewrite 4!mem_cat.
    move/or3P; case=> H; apply/or3P; by [ apply: Or33 | apply: Or32 | apply: Or31 ].
  - apply/allP=> n; case: n => [ ? | g n]; first done.
    move=> nin; move/allP/(_ _ nin): all_3; rewrite 4!mem_cat.
    move/or3P; case=> H; apply/or3P; by [ apply: Or33 | apply: Or32 | apply: Or31 ].
Qed.

Lemma chain_insert_iff :
  forall al ar a,
    chain (al ++ a :: ar) <-> chain (a :: al ++ ar).
Proof.
  move=> al ar a.
  split=> H.
  - rewrite -cat_cons -cat1s -catA.
    by apply: chain_catC3_swap.
  - rewrite -cat1s.
    by apply: chain_catC3_swap.
Qed.

Lemma chain_decided_by_only_name :
  forall actors actors',
    map actor_name actors = map actor_name actors' ->
    chain actors ->
    chain actors'.
Proof.
  move=> ? ? name_eq.
  rewrite/chain.
  by rewrite name_eq.
Qed.
