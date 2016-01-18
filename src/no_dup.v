Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat.
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
  apply/(perm_no_dup (Permutation_sym H1)).
  have child_notin : generated gen parent \notin [:: parent & map actor_name rest].
  - move: fr.
    move/(perm_gen_fresh H0).
    move/gen_fresh_soundness.
    move/(_ parent gen).
    rewrite/name_next/=.
    rewrite in_cons.
    apply; apply/orP; left; done.
  - move: no.
    move/(perm_no_dup H0).
    rewrite/no_dup/=.
    case/andP=> parent_notin u.
    by apply/and3P; split.
Qed.

(* Lemma no_dup_decided_by_only_name : *)
(*   forall actors actors', *)
(*     map actor_name actors = map actor_name actors' -> *)
(*     no_dup actors -> *)
(*     no_dup actors'. *)
(* Proof. *)
(*   rewrite/no_dup. *)
(*   move=> actors actors' name_eq no. *)
(*     by rewrite <- name_eq. *)
(* Qed. *)

(* Lemma name_next_in_name : *)
(*   forall p x actors, *)
(*     p == x.1 -> *)
(*     x \in map name_next actors -> *)
(*     p \in map actor_name actors. *)
(* Proof. *)
(*   move=> p x actors. *)
(*   elim: actors. *)
(*   - move=> H; move=> //=. *)
(*   - move=> a l IH H. *)
(*     simpl in *. *)
(*     do!rewrite in_cons. *)
(*     set H as i; move: i. *)
(*     move/IH=> H1. *)
(*     unfold name_next in *. *)
(*     + case/orP. *)
(*       * move/eqP=> H'. *)
(*         apply/orP. *)
(*         subst; by left. *)
(*       * move=> H'. *)
(*         apply/orP. *)
(*         subst. *)
(*         right. *)
(*           by apply/H1. *)
(* Qed. *)

Lemma no_dup_in_cons :
  forall a c n,
    n \in [seq actor_name i | i <- c] ->
    no_dup (a :: c) ->
    n <> actor_name a.
Proof.
  move=> a c n nin no contra.
  move: no.
  rewrite/no_dup/=.
  case/andP=> ans _.
  by move/negP: ans; apply; rewrite -contra.
Qed.

(* Lemma hoge_child_in : *)
(*   forall c child_gen parent_name parent_next, *)
(*     gen_fresh c -> *)
(*     chain c -> *)
(*     (parent_name, parent_next) \in [seq name_next i | i <- c] -> *)
(*     child_gen < parent_next -> *)
(*     generated child_gen parent_name \in [seq actor_name i | i <- c]. *)
(* Proof. *)
(*   move=> a c. *)
(*   rewrite/gen_fresh/name_next/=. *)
(*   move=> fr ch no. *)
(*   move=> child_gen parent_name parent_next gen_in nn_in. *)
(*   move/(_ child_gen parent_name parent_next): fr; apply. *)
(*   - admit. *)
(*     (* move: gen_in'. *) *)
(*     (* rewrite in_cons. *) *)
(*     (* case/orP=> //. *) *)
(*     (* move=> contra; exfalso. *) *)
(*     (* hoge. *) *)

(*     (* actor_name a \in [seq actor_name i | i <- c] *) *)

(*     (* by move=> contra; exfalso; move/negP: not_child; apply. *) *)
(*   - move: nn_in. *)
(*     rewrite in_cons. *)
(*     case/orP=> //. *)

(*     parent_name != actor_name a *)


(*     move/eqP; case=> contra _; exfalso; move/negP: not_parent; apply. *)
(*     by apply/eqP. *)
(* Qed. *)

Lemma gen_fresh_head :
  forall a c,
    gen_fresh (a :: c) ->
    generated (next_num a) (actor_name a) \notin [seq actor_name i | i <- (a :: c)].
Proof.
  move=> a c fr.
  move/(_ (a :: c) (actor_name a) (next_num a) fr): gen_fresh_soundness; apply.
  rewrite in_cons; rewrite/name_next.
  by apply/orP; left.
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
  move=> child_gen pn px; repeat rewrite in_cons; move=> child_in parent_in.
  move/(_ child_gen pn px): fr.
  apply.
  -





















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


  have fr': gen_fresh c by [].
  move/(perm_gen_fresh perm)/gen_fresh_increase: fr'.



  rewrite/gen_fresh/name_next/= => fr.
  move=> child_gen pn px.
  move/(_ child_gen pn px): fr. (* ? *)

  repeat rewrite in_cons.




  move=> child_in.

  have child_notin : generated parent_next parent_name \notin [seq actor_name i | i <- c].
  move/(_ c parent_name parent_next fr): gen_fresh_soundness; apply.
  apply/(perm_map_in (Permutation_sym perm)).
  rewrite/name_next/=.
  rewrite in_cons; apply/orP; by left.

  have grandchild_notin :
    generated child_gen (generated parent_next parent_name) \notin [seq actor_name i | i <- c]
    by apply/chain_no_parent_no_child.


  move/or3P.
  case.
  - move/eqP=> ppeq; inversion ppeq; clear ppeq; subst.
    exfalso; case/orP: child_in;
    first by move/eqP=> contra; symmetry in contra; apply/(name_not_cycle contra).
    apply/negP.
    rewrite -in_cons.
    apply/negP=> contra.
    move/negP: grandchild_notin; apply.
    by apply/(perm_map_in (Permutation_sym perm))=>/=.
  - move/eqP=> ppeq; inversion ppeq; clear ppeq; subst.
    case cpeq : (child_gen == parent_next).
    + by move/eqP: cpeq=>->.
    + eapply gen_fresh_increase.
      * by apply/(perm_gen_fresh perm).
      * rewrite/=; rewrite in_cons.
        apply/orP; right.
        case/or3P: child_in.
        - move/eqP=> contra; inversion contra; subst; clear contra.
          by exfalso; move/negP: cpeq; apply.
        - by move/eqP=> contra; exfalso; symmetry in contra; apply/(name_not_cycle contra).
        - by apply.
      * rewrite/name_next/=.
        by rewrite in_cons; apply/orP; left.
  - move=> ppin; move: fr.
    rewrite/gen_fresh.
    move/(_ child_gen pn px); apply.
    + apply/(perm_map_in (Permutation_sym perm))=>/=.
      rewrite in_cons.
      move: child_in.
      rewrite -implyNb.
      move/implyP.
      apply.
      apply/negP; move/eqP=> contra; inversion contra; subst; clear contra.

      case cpeq : (child_gen == parent_next).
      *





case cpeq : (child_gen == px).
    + move/eqP: cpeq=> cpeq; subst=> a.

 do 2 rewrite -implyNb in child_in.
    move/implyP: child_in.



      * by move/eqP=> cppp; inversion cppp.
      * by move/eqP=> contra; exfalso; symmetry in contra; apply/(name_not_cycle contra).
      *
    +
    +


  case.
  - (* this case violates `chain` and `gen_fresh` *)
    rewrite/name_next/=.
    repeat rewrite in_cons.

    have child_notin : generated parent_next parent_name \notin (map actor_name c).
    + move/(_ c parent_name parent_next fr): gen_fresh_soundness; apply.
      apply/(perm_map_in (Permutation_sym perm)).
      rewrite/name_next/=.
      rewrite in_cons; apply/orP; by left.
    have no_child_no_grandchild :
      forall g, generated g (generated parent_next parent_name) \notin (map actor_name c)
        by eapply chain_no_parent_no_child.

    case/or3P.
    + move/eqP=> ppeq; inversion ppeq; subst; clear ppeq.
      exfalso; move/negP: (no_child_no_grandchild child_gen); apply.
      apply/(perm_map_in (Permutation_sym perm))=>/=.
      rewrite in_cons; apply/orP; right.
      move: child_in; rewrite in_cons; case/orP.
        by move/eqP=> contra; symmetry in contra; exfalso; eapply name_not_cycle; apply contra.
        by rewrite in_cons; case/orP; [ move/eqP=> contra; symmetry in contra; exfalso; eapply name_not_cycle2; apply contra | done ].
    + move/eqP=> ppeq; inversion ppeq; subst; clear ppeq.
      move/(perm_gen_fresh perm)/gen_fresh_increase: fr.
      move/(_ (parent_cont (generated parent_next parent_name)) parent_behv parent_queue). (* for only match type *)
      rewrite/gen_fresh.
      move/(_ child_gen parent_name parent_next.+1)=>/=.
      rewrite/name_next/=.




      case/or3P.
      * move/eqP=> ppeq; inversion ppeq; subst; clear ppeq.
        exfalso; move/negP: (no_child_no_grandchild child_gen); apply.
        apply/(perm_map_in (Permutation_sym perm))=>/=.
        rewrite in_cons; apply/orP; right.
        move: child_in; rewrite in_cons; case/orP.
          by move/eqP=> contra; symmetry in contra; exfalso; eapply name_not_cycle; apply contra.
          by rewrite in_cons; case/orP; [ move/eqP=> contra; symmetry in contra; exfalso; eapply name_not_cycle2; apply contra | done ].
      * move/eqP=> ppeq; inversion ppeq; subst; clear ppeq.





      move=> <- /= ?; subst.
      exfalso; move/negP: (no_child_no_grandchild child_gen); apply.
      apply/(perm_map_in (Permutation_sym perm)).
      move: child_in.
      repeat rewrite in_cons.
      case/orP; last done.
      by move/eqP=> contra; exfalso; symmetry in contra; eapply name_not_cycle; apply contra.
  - move/(perm_gen_fresh perm)/gen_fresh_increase: fr.
    rewrite/gen_fresh/=.
    move/(_ child_gen child_parent_name parent).

    move=> ? ?; subst=>/=.
    simpl in child_in.
    move/(
    rewrite/gen_fresh.
    move/(_ child_gen parent_name {|
       state_type := parent_st;
       actor_name := parent_name;
       remaining_actions := (n) <- new child_behv with child_ini;
                            parent_cont n;
       next_num := parent_next.+1;
       behv := parent_behv;
       queue := parent_queue |})=>/=.
    apply; [ | by left | done ].
    move: child_in=>/=.
    rewrite in_cons.
    have neq : child_gen != parent_next.


    move: child_in.
    rewrite in_cons.
    case/orP.

    + by move/eqP=> contra; symmetry in contra; exfalso; eapply name_not_cycle; apply contra.
    +




(*   move=> sendings sendings' actors actors' child. *)
(*   move=> ch fr no tr. *)
(*   inversion tr; subst. *)
(*   constructor. *)
(*   (* assert (ch' : chain actors'); *) *)
(*   (* apply new_trans_chain with (msgs := msgs) (msgs' := msgs') (actors' := actors') in ch; auto. *) *)
(*   (* 1. gen_fresh の補題「gen_number が増えても、gen_fresh は成り立つ」(gen_fresh_increase) を使う *) *)
(*   (* 2. chain の補題「子がいないなら孫もいない」(no_child_no_grandchild) もしくは「いないやつの子はいない」(no_actor_no_child) を使う??? *) *)
(*   (* 3. no_dup の条件を使う *) *)
(*   - move/gen_fresh_increase: fr. *)
(*     apply/gen_fresh_decided_by_only_name_and_next_number. *)
(*     by rewrite/name_next; repeat (rewrite map_cat) => /=. *)
(*   - move=> yet le. *)
(*     rewrite map_cat mem_cat =>/=; rewrite in_cons. *)
(*     move/gen_fresh_insert_iff: fr=>fr. *)
(*     move/chain_insert_iff: ch=> ch. *)
(*     inversion fr; subst. *)
(*     move/(_ gen): H4=> H4. *)
(*     have: gen <= gen by exact: leqnn. *)
(*     move/H4. *)
(*     move/head_leaf_child_not_in: ch=> /=. *)
(*     move/(_ gen yet)=> imp. *)
(*     move/imp. *)
(*     rewrite map_cat mem_cat. *)
(*     case/norP=> in_l in_r. *)
(*     apply/or3P; case. *)
(*     + by apply/negP. *)
(*     + move/eqP=> contra; symmetry in contra; by apply: (name_not_cycle2 contra). *)
(*     + by apply/negP. *)
(*   - rewrite map_cat all_cat =>/=. *)
(*     have: all (fun nn => parent != nn.1) (map name_next actors_l) && *)
(*               all (fun nn => parent != nn.1) (map name_next actors_r). *)
(*     { *)
(*       move: no. *)
(*       rewrite/no_dup. *)
(*       rewrite map_cat; simpl. *)
(*       rewrite cat_uniq cons_uniq. *)
(*       case/and4P=> uniq_l has_p notin_p uniq_r. *)
(*       apply/andP; split. *)
(*       * apply/allP=> x all_p. *)
(*         apply/negP=> contra. *)
(*         move/negP: has_p; apply. *)
(*         apply/hasP. *)
(*         exists parent. *)
(*         - rewrite in_cons; apply/orP; left; exact: eq_refl. *)
(*         - apply: name_next_in_name; done. *)
(*       * apply/allP=> x in_p. *)
(*         apply/negP=> contra. *)
(*         move/negP: notin_p; apply. *)
(*         apply: name_next_in_name; done. *)
(*     } *)
(*     case/andP=> allnot_l allnot_r. *)
(*     apply/and3P; do!split. *)
(*     + apply/allP=> x in_p; apply/implyP=> peq. *)
(*       by move/allP/(_ x in_p)/negP: allnot_l. *)
(*     + apply/implyP=> _. *)
(*       exact: ltnSn. *)
(*     + apply/allP=> x in_p; apply/implyP=> peq. *)
(*       by move/allP/(_ x in_p)/negP: allnot_r. *)
(* Qed. *)
