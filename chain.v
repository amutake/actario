Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Import ListNotations.

Require Import util syntax semantics name_dec.

(* 自分の親も必ず入っている (全部つながっている) *)
(* chain という名前微妙？ *)
Definition chain (actors : list actor) : Prop :=
  Forall (fun n => G.pprop_n n (fun p => In p (map G.n actors))) (map G.n actors).

Hint Unfold chain.

Lemma new_trans_parent_exists :
  forall msgs msgs' actors new_actor actors',
    trans New (conf msgs actors) (conf msgs' (new_actor :: actors')) ->
    G.pprop new_actor (fun p => In p (map G.n actors')). (* new_actor の名前が toplevel になることはありえないので大丈夫。だけど、ちゃんとしたほうがいい？ *)
Proof.
  intros msgs msgs' actors new_actor actors' tr.
  destruct new_actor as [ new_n new_a new_b new_s ].
  simpl.

  inversion tr; subst.
  clear tr.
  rewrite map_app.
  apply in_app_iff.
  right; simpl; left; auto.
Qed.

Lemma new_trans_parent_exists' :
  forall msgs msgs' actors new_actor actors',
    trans New (conf msgs actors) (conf msgs' (new_actor :: actors')) ->
    G.pprop new_actor (fun p => In p (map G.n (new_actor :: actors'))).
Proof.
  intros msgs msgs' actors new_actor actors' tr.
  apply new_trans_parent_exists in tr.
  destruct new_actor as [ n a b s ].
  simpl in *.
  destruct n; [ auto | right; auto ].
Qed.

Lemma F_or {A B} :
  forall a P Q (f : A -> B),
    (fun b => P b \/ Q b) (f a) <-> P (f a) \/ Q (f a).
Proof.
  intros a P Q f.
  split; intro H; auto.
Qed.

Lemma Forall_inner_or_intror {A B} :
  forall xs P Q (f : A -> B),
    Forall (fun x => Q (f x)) xs ->
    Forall (fun x => P (f x) \/ Q (f x)) xs.
Proof.
  intros xs P Q f H.
  induction xs; auto.
  apply Forall_cons_iff.
  apply Forall_cons_iff in H.
  destruct H as [ Hh Ht ].
  split; [ right; auto | auto ].
Qed.

Lemma pprop_or : forall a P Q, G.pprop a (fun p => P p \/ Q p) -> G.pprop a P \/ G.pprop a Q.
Proof.
  intros a P Q H.
  destruct a as [ n a b s ].
  simpl in *.
  destruct n as [ | p g ]; auto.
Qed.

Lemma Forall_pprop_or_r : forall actors P Q,
                            Forall (fun a => G.pprop a Q) actors ->
                            Forall (fun a => G.pprop a (fun p => P p \/ Q p)) actors.
Proof.
  intros actors P Q H.
  induction actors as [ | a as' ]; auto.
  apply Forall_cons_iff.
  apply Forall_cons_iff in H.
  destruct H as [ Hh Ht ].
  destruct a as [ n a b s ].
  destruct n as [ | p g ]; simpl in *.
  - split; auto.
  - split; auto.
Qed.

Lemma Forall_pprop_n_or_r :
  forall names P Q,
    Forall (fun n => G.pprop_n n Q) names ->
    Forall (fun n => G.pprop_n n (fun p => P p \/ Q p)) names.
Proof.
  intros names P Q H.
  induction names as [ | h t ]; auto.
  apply Forall_cons_iff.
  apply Forall_cons_iff in H.
  destruct H as [ Hh Ht ].
  destruct h as [ | p g ]; simpl in *.
  - split; auto.
  - split; auto.
Qed.

Lemma In_name :
  forall actor actors,
    In actor actors -> In (G.n actor) (map G.n actors).
Proof.
  intros actor actors ina.
  induction actors; simpl; auto.
  simpl in ina.
  destruct ina as [ ina | ina ]; [ left; subst; auto | ].
  right; apply IHactors; auto.
Qed.

Lemma new_trans_chain :
  forall msgs msgs' actors actors',
    chain actors ->
    trans New (conf msgs actors) (conf msgs' actors') ->
    chain actors'.
Proof.
  intros msgs msgs' actors actors' ch tr.
  inversion tr; subst.
  apply new_trans_parent_exists' in tr.
  unfold chain.
  simpl.
  apply Forall_cons_iff.
  split; auto.

  unfold chain in ch.
  rewrite map_app in *; simpl in *.
  apply Forall_app_iff in ch.
  destruct ch as [ ch_l ch' ].
  apply Forall_cons_iff in ch'.
  destruct ch' as [ ch_m ch_r ].

  apply Forall_app_iff.
  repeat (rewrite map_app in *; simpl in *; idtac).

  split.
  - apply Forall_pprop_n_or_r; auto.
  - apply Forall_cons_iff.
    split.
    + destruct addr; auto.
      simpl; auto.
    + apply Forall_pprop_n_or_r; auto.
Qed.

Lemma head_leaf_child_not_in :
  forall a actors gen gen',
    chain (a :: actors) ->
    ~ In (generated (G.n a) gen) (map G.n actors) ->
    ~ In (generated (generated (G.n a) gen) gen') (map G.n actors).
Proof.
  (* 孫がいたら矛盾 *)
  (* 1. actors の中に、((n(a), gen), gen') がいる *)
  (* 2. ((n(a), gen), gen') の親は (n(a), gen) *)
  (* 3. chain (a :: actors) から、forall a' \in actors, p(a') \in names(a :: actors) *)
  (* 4. 3 で a' = ((n(a), gen), gen') のとき、p(a') = (n(a), gen) = n(a) \/ (n(a), gen) \in names(as) となるが、左は成り立たないので、(n(a), gen) \in names(actors) が成り立つ *)
  (* 5. 仮定に (n(a), gen) \nin names(actors) があるので矛盾 *)
  intros a actors gen gen' ch nin c.
  unfold chain in ch; simpl in ch.
  apply Forall_cons_iff in ch.
  destruct ch as [ ch_a ch_as ].
  simpl in ch_as.
  assert (ain : exists actor,
                  G.n actor = generated (generated (G.n a) gen) gen' /\
                  In actor actors).
  - clear nin ch_as ch_a.
    induction actors as [ | hd tl ]; [ inversion c | ].
    simpl in c.
    destruct c as [ c | c ].
    + exists hd.
      split; auto.
      simpl; left; auto.
    + simpl.
      apply IHtl in c.
      destruct c as [ actor c ].
      destruct c as [ aeq ina ].
      exists actor.
      split; auto.
  - destruct ain as [ actor ain ].
    destruct ain as [ actor_name actor_in ].
    eapply Forall_forall in ch_as; [ | apply In_name in actor_in; apply actor_in ].
    destruct actor as [ n ].
    simpl in ch_as.
    destruct n as [ | p g' ]; simpl in actor_name.
    + inversion actor_name.
    + inversion actor_name; subst.
      destruct ch_as as [ ch_as | ch_as ].
      * apply name_not_cycle in ch_as; auto.
      * auto.
Qed.

Lemma chain_insert_iff :
  forall al ar a,
    chain (al ++ a :: ar) <-> chain (a :: al ++ ar).
Proof.
  intros al ar a.
  split; intro H.
  - unfold chain in *; simpl in *; rewrite map_app in *; simpl in *.

    apply Forall_app_iff in H.
    destruct H  as [ Hl H ].
    apply Forall_cons_iff in H.
    destruct H as [ H Hr ].
    apply Forall_cons_iff.
    split.
    + destruct a as [ n a q s ]; simpl in *.
      destruct n as [ | p g ]; simpl in *; auto.
      apply in_app_iff in H.
      destruct H as [ H | H ];
        [ right; apply in_app_iff; left; auto
        | simpl in H; destruct H as [ H | H ];
          [ left; symmetry; auto
          | right; apply in_app_iff; right; auto
          ]
        ].
    + apply Forall_app_iff.
      split.
      * apply Forall_forall.
        intros x xin.
        eapply Forall_forall in Hl.
        { instantiate (1 := x) in Hl.
          destruct x as [ | xp xg ]; simpl in *; auto.
          apply in_app_iff in Hl.
          simpl in Hl.
          destruct Hl; [ right; apply in_app_iff; left; auto | ].
          destruct H0; auto.
          right; apply in_app_iff; right; auto.
        }
        auto.
      * apply Forall_forall.
        intros x xin.
        eapply Forall_forall in Hr.
        { instantiate (1 := x) in Hr.
          destruct x as [ | xp xg ]; simpl in *; auto.
          apply in_app_iff in Hr.
          simpl in Hr.
          destruct Hr; [ right; apply in_app_iff; left; auto | ].
          destruct H0; auto.
          right; apply in_app_iff; right; auto.
        }
        auto.
  - unfold chain in *; repeat (rewrite map_app in *; simpl in *; idtac).
    apply Forall_cons_iff in H.
    destruct H as [ H H' ].
    apply Forall_app_iff in H'.
    destruct H' as [ Hl Hr ].

    apply Forall_app_iff.
    repeat (rewrite map_app in *; simpl in *; idtac).
    split.
    + apply Forall_forall.
      intros x xin.
      eapply Forall_forall in Hl.
      * instantiate (1 := x) in Hl.
        destruct x as [ | xp xg ]; simpl in *; auto.
        apply in_app_iff.
        destruct Hl; [ right; simpl; left; auto | ].
        apply in_app_iff in H0.
        destruct H0; auto.
        right; simpl; right; auto.
      * auto.
    + apply Forall_cons_iff.
      split.
      * destruct a.
        simpl in *.
        destruct n; auto.
        apply in_app_iff.
        simpl.
        destruct H; auto.
        apply in_app_iff in H.
        destruct H; auto.
      * apply Forall_forall.
        intros x xin.
        eapply Forall_forall in Hr.
        { instantiate (1 := x) in Hr.
          destruct x as [ | xp xg ]; simpl in *; auto.
          apply in_app_iff.
          simpl.
          destruct Hr; [ right; left; auto | ].
          apply in_app_iff in H0.
          destruct H0; auto.
        }
        auto.
Qed.

Lemma chain_related_only_name :
  forall actors actors',
    map G.n actors = map G.n actors' ->
    chain actors ->
    chain actors'.
Proof.
  intros actors actors' name_eq ch.
  unfold chain in *.
  rewrite name_eq in ch; auto.
Qed.
