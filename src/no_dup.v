Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat.

Require Import util syntax semantics name_dec chain gen_fresh.

(* list actor 内のアクターについて、アクターの名前が被ってない *)
Definition no_dup (actors : seq actor) := uniq (map actor_name actors).

Lemma no_dup_decided_by_only_name :
  forall actors actors',
    map actor_name actors = map actor_name actors' ->
    no_dup actors ->
    no_dup actors'.
Proof.
  rewrite/no_dup.
  move=> actors actors' name_eq no.
    by rewrite <- name_eq.
Qed.

Lemma name_next_in_name :
  forall p x actors,
    p == x.1 ->
    x \in map name_next actors ->
    p \in map actor_name actors.
Proof.
  move=> p x actors.
  elim: actors.
  - move=> H; move=> //=.
  - move=> a l IH H.
    simpl in *.
    do!rewrite in_cons.
    set H as i; move: i.
    move/IH=> H1.
    unfold name_next in *.
    + case/orP.
      * move/eqP=> H'.
        apply/orP.
        subst; by left.
      * move=> H'.
        apply/orP.
        subst.
        right.
          by apply/H1.
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
  forall sendings sendings' actors actors' child,
    chain actors ->
    gen_fresh actors ->
    no_dup actors ->
    (sendings >< actors) ~(New child)~> (sendings' >< actors') ->
    gen_fresh actors'.
Proof.
  move=> sendings sendings' actors actors' child.
  move=> ch fr no tr.
  inversion tr; subst.
  constructor.
  (* assert (ch' : chain actors'); *)
  (* apply new_trans_chain with (msgs := msgs) (msgs' := msgs') (actors' := actors') in ch; auto. *)
  (* 1. gen_fresh の補題「gen_number が増えても、gen_fresh は成り立つ」(gen_fresh_increase) を使う *)
  (* 2. chain の補題「子がいないなら孫もいない」(no_child_no_grandchild) もしくは「いないやつの子はいない」(no_actor_no_child) を使う??? *)
  (* 3. no_dup の条件を使う *)
  - move/gen_fresh_increase: fr.
    apply/gen_fresh_decided_by_only_name_and_next_number.
    by rewrite/name_next; repeat (rewrite map_cat) => /=.
  - move=> yet le.
    rewrite map_cat mem_cat =>/=; rewrite in_cons.
    move/gen_fresh_insert_iff: fr=>fr.
    move/chain_insert_iff: ch=> ch.
    inversion fr; subst.
    move/(_ gen): H4=> H4.
    have: gen <= gen by exact: leqnn.
    move/H4.
    move/head_leaf_child_not_in: ch=> /=.
    move/(_ gen yet)=> imp.
    move/imp.
    rewrite map_cat mem_cat.
    case/norP=> in_l in_r.
    apply/or3P; case.
    + by apply/negP.
    + move/eqP=> contra; symmetry in contra; by apply: (name_not_cycle2 contra).
    + by apply/negP.
  - rewrite map_cat all_cat =>/=.
    have: all (fun nn => parent != nn.1) (map name_next actors_l) &&
              all (fun nn => parent != nn.1) (map name_next actors_r).
    {
      move: no.
      rewrite/no_dup.
      rewrite map_cat; simpl.
      rewrite cat_uniq cons_uniq.
      case/and4P=> uniq_l has_p notin_p uniq_r.
      apply/andP; split.
      * apply/allP=> x all_p.
        apply/negP=> contra.
        move/negP: has_p; apply.
        apply/hasP.
        exists parent.
        - rewrite in_cons; apply/orP; left; exact: eq_refl.
        - apply: name_next_in_name; done.
      * apply/allP=> x in_p.
        apply/negP=> contra.
        move/negP: notin_p; apply.
        apply: name_next_in_name; done.
    }
    case/andP=> allnot_l allnot_r.
    apply/and3P; do!split.
    + apply/allP=> x in_p; apply/implyP=> peq.
      by move/allP/(_ x in_p)/negP: allnot_l.
    + apply/implyP=> _.
      exact: ltnSn.
    + apply/allP=> x in_p; apply/implyP=> peq.
      by move/allP/(_ x in_p)/negP: allnot_r.
Qed.

Lemma new_trans_no_dup :
  forall msgs msgs' actors actors' child,
    gen_fresh actors ->
    no_dup actors ->
    (msgs >< actors) ~(New child)~> (msgs' >< actors') ->
    no_dup actors'.
Proof.
  move=> msgs msgs' actors actors' child fr no tr.
  inversion tr; subst.
  eapply new_trans_fresh with (actor0 := Build_actor (generated gen parent) (become behv) 0) in fr; last by exact: tr.
  - rewrite/no_dup/=.
    apply/andP; split.
    + exact: fr.
    + move: no; rewrite/no_dup.
      do!rewrite map_cat =>/=.
      done.
Qed.
