Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat.
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

(* Lemma chain_chain' : *)
(*   forall s, chain s -> chain' s. *)
(* Proof. *)
(*   elim. *)
(*   - done. *)
(*   - rewrite/chain/chain'. *)
(*     move=> a l IH /= allp n p inp. *)
(*     rewrite in_cons; apply/orP. *)
(*     move: allp. *)
(*     case/andP. *)
(*     case_eq (actor_name a). *)
(*     + move=> s aeq _. *)
(*       rewrite aeq in inp. *)


(*   move=> s allp n p inp. *)















(*   elim. *)
(*   - by move=> s'; move/Permutation_nil=> ->. *)
(*   - *)
(*   elim; elim. *)
(*   move=> s s'. *)
(*   rewrite/chain'=> perm. *)
(*   rewrite (perm_map_in_eq actor_name _ perm). *)
(*   - done. *)
(*   - *)






(* Inductive chain' : config -> Prop := *)
(* | chain_nil : chain' [::] *)
(* | chain_toplevel : forall st m a n b q, *)
(*     chain *)

(* Lemma perm_chain : *)
(*   forall s s', *)
(*     Permutation s s' -> *)
(*     chain s -> *)
(*     chain s'. *)
(* Proof. *)
(*   move=> s s'; elim. *)
(*   - done. *)
(*   - move=> x l l' perm IH. *)
(*     rewrite/chain/=. *)
(*     case: x=> /= _ n _ _ _ _. *)
(*     case: n=> [ m | n p ]. *)
(*     case/andP=> _ outer. *)





(*   elim. *)
(*   - move=> s perm H. *)
(*       by move/Permutation_nil: perm=> ->. *)
(*   - move=> a s IH s'; move: a s IH. *)
(*     elim: s'; first done. *)
(*     move=> a' s' IH'. *)
(*     move=> a s IH perm H. *)

(*   move=> s s' perm. *)
(*   rewrite/chain. *)





(*   - done. *)
(*   - move=> x l l' perm. *)
(*     case: x. *)
(*     rewrite/chain/=. *)
(*     move=> _ n _ _ _ _. *)


(* Lemma new_trans_parent_exists : *)
(*   forall actors actors' child, *)
(*     child \in map actor_name actors' -> *)
(*     actors ~(New child)~> actors' -> *)
(*     if child is generated _ p then *)
(*       p \in (map actor_name actors') *)
(*     else false. (* new_actor の名前が toplevel になることはありえないので大丈夫 *) *)
(* Proof. *)
(*   move=> actors actors'. *)
(*   case. *)
(*   - move=> m H tr. *)
(*     inversion tr. *)
(*   - move=> g n H tr. *)
(*     inversion tr; subst; clear tr. *)
(*     eapply perm_map_in. *)
(*     + apply Permutation_sym; apply H5. *)
(*     + move=>/=; repeat rewrite in_cons; apply/or3P. *)
(*       by apply Or32. *)
(* Qed. *)

(* Lemma new_trans_parent_exists' : *)
(*   forall actors actors' new_actor child, *)
(*     actor_name new_actor = child -> *)
(*     actors ~(New child)~> (new_actor :: actors') -> *)
(*     if child is generated _ p then *)
(*       p \in (map actor_name (new_actor :: actors')) *)
(*     else false. *)
(* Proof. *)
(*   move=> actors actors' new_actor child H. *)
(*   apply: new_trans_parent_exists. *)
(*   rewrite in_cons. *)
(*   move: H =>->. *)
(*   rewrite eq_refl. *)
(*   exact: orTb. *)
(* Qed. *)

(* Lemma new_trans_chain : *)
(*   forall actors actors' child, *)
(*     chain actors -> *)
(*     (actors) ~(New child)~> (actors') -> *)
(*     chain actors'. *)
(* Proof. *)
(*   move=> actors actors' child ch tr. *)
(*   move: ch. *)
(*   rewrite/chain. *)
(*   inversion tr; subst; clear tr. *)
(*   move/(perm_map_all H0)=> /=. *)
(*   case/andP. *)
(*   case_eq parent=> s parent_eq; subst. *)
(*   - move=> _ H. *)
(*     apply/(perm_map_all (Permutation_sym H1))=> /=. *)
(*     apply/andP; split. *)
(*     + apply/(perm_map_in (Permutation_sym H1))=> /=. *)
(*       repeat rewrite in_cons. *)
(*       apply/or3P; *)


(*   move/(trans_perm_r H1): tr. *)
(*   move/new_trans_parent_exists'=> /=. *)
(*   move/(_ Logic.eq_refl). *)
(*   rewrite/chain/=. *)
(*   have ggpeq : generated gen parent = generated gen parent by reflexivity. *)
(*   move/(_ ggpeq)=> pin_p. *)
(*   eapply perm_map_all. *)
(*   - move/Permutation_sym: H1; apply. *)
(*   - simpl. *)
(*     apply/andP; split. *)
(*     + eapply perm_map_in. *)
(*       * move/Permutation_sym: H1; apply. *)
(*       * simpl. *)
(*         repeat rewrite in_cons. *)
(*         by apply/or3P; constructor 2. *)
(*     + apply/andP; split. *)
(*       * case_eq parent. *)
(*         - by move=> ? ?. *)
(*         - move=> n pp peq; subst. *)
(*           apply/(perm_map_in (Permutation_sym H1)) => /=. *)
(*           rewrite in_cons; apply/orP; right. *)

(*         move: ch. *)
(*         rewrite/chain/=; repeat (rewrite map_cat /=). *)
(*         move/(perm_map_all H0)/andP. *)
(*         case=> ? ?. *)
(*         rewrite 2!all_cat /=. *)
(*   move/and3P. *)
(*   case=> ch_l ch_p ch_r. *)
(*   apply/and3P. *)
(*   split. *)
(*   - apply/allP=> x xin. *)
(*     move/allP/(_ x xin): ch_l. *)
(*     move: xin; case: x; first done. *)
(*     move=> g n xin H. *)
(*     by rewrite in_cons; apply/orP; right. *)
(*   - destruct parent; first done. *)
(*     by rewrite in_cons; apply/orP; right. *)
(*   - apply/allP=> x xin. *)
(*     move/allP/(_ x xin): ch_r. *)
(*     move: xin; case: x; first done. *)
(*     move=> g n xin H. *)
(*     by rewrite in_cons; apply/orP; right. *)
(* Qed. *)

(* Lemma head_leaf_child_not_in : *)
(*   forall a actors gen gen', *)
(*     chain (a :: actors) -> *)
(*     (generated gen (actor_name a)) \notin (map actor_name actors) -> *)
(*     (generated gen' (generated gen (actor_name a))) \notin (map actor_name actors). *)
(* Proof. *)
(*   (* 孫がいたら矛盾 *) *)
(*   (* 1. actors の中に、((n(a), gen), gen') がいる *) *)
(*   (* 2. ((n(a), gen), gen') の親は (n(a), gen) *) *)
(*   (* 3. chain (a :: actors) から、forall a' \in actors, p(a') \in names(a :: actors) *) *)
(*   (* 4. 3 で a' = ((n(a), gen), gen') のとき、p(a') = (n(a), gen) = n(a) \/ (n(a), gen) \in names(as) となるが、左は成り立たないので、(n(a), gen) \in names(actors) が成り立つ *) *)
(*   (* 5. 仮定に (n(a), gen) \nin names(actors) があるので矛盾 *) *)
(*   case=> /= name actions next actors gen gen' ch notin. *)
(*   apply/negP=> gg_in; move/negP: notin; apply. *)
(*   move: ch; rewrite/chain/=; case/andP=> a_case all_p. *)
(*   have: generated gen name \in name :: map actor_name actors *)
(*     by move/allP/(_ (generated gen' (generated gen name)) gg_in): all_p. *)
(*   rewrite in_cons; move/orP; case; last done. *)
(*   move/eqP=> contra. *)
(*   symmetry in contra. *)
(*   by move: (name_not_cycle contra). *)
(* Qed. *)

(* Lemma chain_catC3_swap : *)
(*   forall a1 a2 a3, *)
(*     chain (a1 ++ a2 ++ a3) -> chain (a2 ++ a1 ++ a3). *)
(* Proof. *)
(*   move=> a1 a2 a3. *)
(*   rewrite/chain. *)
(*   repeat (rewrite (map_cat, all_cat) /=). *)
(*   case/and3P=> all_1 all_2 all_3. *)
(*   apply/and3P; split. *)
(*   - apply/allP=> n; case: n => [ ? | g n ]; first done. *)
(*     move=> nin; move/allP/(_ _ nin): all_2; rewrite 4!mem_cat. *)
(*     move/or3P; case=> H; apply/or3P; by [ apply: Or33 | apply: Or32 | apply: Or31 ]. *)
(*   - apply/allP=> n; case: n => [ ? | g n]; first done. *)
(*     move=> nin; move/allP/(_ _ nin): all_1; rewrite 4!mem_cat. *)
(*     move/or3P; case=> H; apply/or3P; by [ apply: Or33 | apply: Or32 | apply: Or31 ]. *)
(*   - apply/allP=> n; case: n => [ ? | g n]; first done. *)
(*     move=> nin; move/allP/(_ _ nin): all_3; rewrite 4!mem_cat. *)
(*     move/or3P; case=> H; apply/or3P; by [ apply: Or33 | apply: Or32 | apply: Or31 ]. *)
(* Qed. *)

(* Lemma chain_insert_iff : *)
(*   forall al ar a, *)
(*     chain (al ++ a :: ar) <-> chain (a :: al ++ ar). *)
(* Proof. *)
(*   move=> al ar a. *)
(*   split=> H. *)
(*   - rewrite -cat_cons -cat1s -catA. *)
(*     by apply: chain_catC3_swap. *)
(*   - rewrite -cat1s. *)
(*     by apply: chain_catC3_swap. *)
(* Qed. *)

(* Lemma chain_decided_by_only_name : *)
(*   forall actors actors', *)
(*     map actor_name actors = map actor_name actors' -> *)
(*     chain actors -> *)
(*     chain actors'. *)
(* Proof. *)
(*   move=> ? ? name_eq. *)
(*   rewrite/chain. *)
(*   by rewrite name_eq. *)
(* Qed. *)
