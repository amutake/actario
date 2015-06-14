Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import util syntax semantics name_dec chain.

(**
 * アクターのリストに、以下の様なアクターはいない
 * 1. そのリストに現れる任意のアクターについて、そのアクターの生成番号的にまだ生成していないはずの名前を持つアクターは、そのリストには現れない
 *
 * つまり、これが成り立っていれば必ず fresh なアクターを生成できる
 *)
Inductive gen_fresh : list actor -> Prop :=
| gen_fresh_nil : gen_fresh []
| gen_fresh_cons :
    forall actors name actions behv gen_num,
      gen_fresh actors ->
      (* 1. 先頭に追加するやつの、生成番号的にまだ生成していないはずの名前は、これまでに出てきていない *)
      (forall yet_num, gen_num <= yet_num -> ~ In (generated name yet_num) (map G.n actors)) ->
      (* 2. 先頭に追加するやつは、これまででてきたどのアクターについても、生成番号的にまだ生成していないはずのアクターではない *)
      Forall (fun act =>
                match name with
                  | toplevel _ => True
                  | generated parent gened_num =>
                    match act with
                      | actor_state name' _ _ number' =>
                        parent = name' -> (* そのアクターが親ならば、 *)
                        gened_num < number' (* 必ずそのアクターが以前に生成したもの *)
                    end
                end) actors ->
      gen_fresh (actor_state name actions behv gen_num :: actors).

Hint Constructors gen_fresh.

(* weak trans invariant property (app -> and) *)
Lemma gen_fresh_app_and :
  forall actors_l actors_r,
    gen_fresh (actors_l ++ actors_r) ->
    gen_fresh actors_l /\ gen_fresh actors_r.
Proof.
  intros actors_l actors_r H.
  induction actors_l.
  - simpl in H.
    split; auto.
  - inversion H.
    + apply IHactors_l in H2.
      destruct H2 as [ IHl IHr ].
      split; auto.
      constructor; auto.
      * intros yet_num Hle contra.
        rewrite map_app in H3.
        apply H3 in Hle.
        apply Hle.
        apply in_app_iff.
        left; auto.
      * apply Forall_app_iff in H4.
        destruct H4; auto.
Qed.

(* weak trans invariant's property (remove) *)
Lemma gen_fresh_remove :
  forall actors_l actor actors_r,
    gen_fresh (actors_l ++ actor :: actors_r) ->
    gen_fresh (actors_l ++ actors_r).
Proof.
  intros actors_l actor actors_r lmr.
  assert (lmr' : gen_fresh (actors_l ++ actor :: actors_r)); auto.
  apply gen_fresh_app_and in lmr'.
  destruct lmr' as [ l mr ].
  rewrite app_cons in mr.
  apply gen_fresh_app_and in mr.
  destruct mr as [ m r ].
  induction actors_l.
  - simpl; auto.
  - simpl.
    destruct a.
    constructor.
    + apply IHactors_l; [ inversion lmr; auto | inversion l; auto ].
    + intros yet_num lt_num contra.
      inversion lmr; subst.
      apply H5 in lt_num.
      apply lt_num.
      rewrite map_app in contra.
      rewrite map_app; simpl.
      apply in_app_iff.
      apply in_app_iff in contra.
      destruct contra as [ contra | contra ]; [ left; auto | right ].
      rewrite app_cons.
      apply in_app_iff.
      right; auto.
    + apply Forall_app_iff.
      split.
      * inversion l; subst; auto.
      * inversion lmr; subst.
        apply Forall_app_iff in H6.
        destruct H6 as [ Hl Htmp ].
        rewrite app_cons in Htmp.
        apply Forall_app_iff in Htmp.
        destruct Htmp as [ Hm Hr ].
        auto.
Qed.

Lemma gen_fresh_swap_two :
  forall actor_l actor_r,
    gen_fresh [actor_l; actor_r] ->
    gen_fresh [actor_r; actor_l].
Proof.
  intros actor_l actor_r H.
  inversion H; subst.
  destruct actor_r.
  constructor.
  - constructor; auto.
  - intros yet_num le contra.
    apply Forall_single in H4.
    destruct name.
    + simpl in contra.
      destruct contra as [ c | c ]; [ inversion c | auto ].
    + simpl in contra.
      destruct contra as [ c | c ]; [ inversion c | auto ].
      apply H4 in H1.
      subst.
      apply Lt.le_not_lt in le.
      apply le; auto.
  - apply Forall_single.
    destruct n; auto.
    intro eq.
    subst.
    simpl in H3.
    apply Forall_single in H4.
    destruct (Compare_dec.le_lt_dec gen_num g0). (* これが鍵だった *)
    + apply H3 in l0.
      exfalso; apply l0.
      left; auto.
    + auto.
Qed.

Lemma gen_fresh_swap_head :
  forall actor1 actor2 actors,
    gen_fresh (actor1 :: actor2 :: actors) ->
    gen_fresh (actor2 :: actor1 :: actors).
Proof.
  intros a1 a2 actors H.
  inversion H; subst.
  clear H.
  inversion H2; subst.
  clear H2.

  rename H3 into H2.
  rename H4 into H3.
  rename H1 into H1_1.
  rename H5 into H1_2.
  rename H6 into H1_3.

  rename name0 into name_a2.
  rename gen_num0 into snum_a2.
  rename name into name_a1.
  rename gen_num into snum_a1.

  remember (actor_state name_a1 actions behv snum_a1) as a1.
  remember (actor_state name_a2 actions0 behv0 snum_a2) as a2.

  (* 1-1 *)
  assert (G1_1 : gen_fresh actors); auto.

  (* 1-2 *)
  assert (G1_2 : forall g, snum_a1 <= g -> ~ In (generated name_a1 g) (map G.n actors)).
  {
    intros g le c.
    apply H2 in le.
    simpl in le.
    apply le.
    right; auto.
  }

  (* 1-3 *)
  assert (G1_3 : Forall (fun a => G.pgprop a1 (fun p g => match a with
                                                            | actor_state an _ _ ag => p = an -> g < ag
                                                          end)) actors).
  {
    apply Forall_cons_iff in H3.
    destruct H3 as [ _ H3_2 ].
    rewrite Heqa1; simpl.
    auto.
  }

  (* 2 *)
  assert (G2 : forall g, G.s a2 <= g ->
                         generated (G.n a2) g <> G.n a1 /\
                         ~ In (generated (G.n a2) g) (map G.n actors)).
  {
    intros g le.
    split.
    (* H3 を使う *)
    - intro c.
      destruct name_a1 as [ | p_a1 g_a1 ].
      + rewrite Heqa1 in c.
        simpl in c.
        inversion c.
      + rewrite Heqa1 in c.
        rewrite Heqa2 in c.
        simpl in c.
        inversion c; subst.
        simpl in le.
        apply Forall_cons_iff in H3.
        destruct H3 as [ H3 _ ].
        apply Lt.le_not_lt in le.
        apply le; apply H3; auto.
    (* H1_2 を使う *)
    - intro c.
      rewrite Heqa2 in le.
      rewrite Heqa2 in c.
      simpl in le.
      apply H1_2 in le.
      apply le; auto.
  }

  (* 2 *)
  assert (G3 :
            G.pgprop a2 (fun p g => p = G.n a1 -> g < G.s a1) /\
            Forall (fun a => G.pgprop a2 (fun p g => match a with
                                                     | actor_state an _ _ ag => p = an -> g < ag
                                                   end)) actors).
  {
    split.
    (* H2 *)
    - rewrite Heqa2.
      rewrite Heqa1.
      simpl.
      destruct name_a2 as [ | parent_a2 gened_a2 ]; auto.
      intros peq.
      destruct (Compare_dec.le_lt_dec snum_a1 gened_a2); auto.
      exfalso.
      apply H2 in l.
      apply l.
      rewrite Heqa2.
      simpl.
      left; rewrite peq; auto.
    (* H1_3 *)
    - rewrite Heqa2.
      simpl.
      destruct name_a2; auto.
  }

  (* 合体 *)
  subst; simpl in *.
  constructor.
  - constructor.
    + apply G1_1.
    + apply G1_2.
    + apply G1_3.
  - intros g le.
    apply NotIn_cons_iff.
    apply G2; auto.
  - apply Forall_cons_iff.
    apply G3.
Qed.

Lemma gen_fresh_insert :
  forall actor actors_l actors_r,
    gen_fresh (actor :: (actors_l ++ actors_r)) ->
    gen_fresh (actors_l ++ actor :: actors_r).
Proof.
  intros a al ar H.
  induction al as [ | al_h al_t IH ].
  - simpl in *; auto.
  - simpl in H.
    apply gen_fresh_swap_head in H.

    (* 準備 *)
    inversion_clear H as [ | actors name actions behv gen_num H1 H2 H3 ].
    clear al_h.
    remember (actor_state name actions behv gen_num) as al_h.
    simpl in *.

    rewrite app_cons in H3.
    apply Forall_app_iff in H3.
    destruct H3 as [ H3_1 H3' ].
    apply Forall_app_iff in H3'.
    destruct H3' as [ H3_2 H3_3 ].

    apply Forall_single in H3_1.

    (* 1 *)
    assert (G1 : gen_fresh (al_t ++ a :: ar)); auto.

    (* 2-1 *)
    assert (G2_1 : forall g, G.s al_h <= g -> ~ In (generated (G.n al_h) g) (map G.n al_t)).
    {
      rewrite Heqal_h.
      simpl.
      intros g le c.
      apply H2 in le.
      apply le.
      right; rewrite map_app.
      apply in_app_iff.
      left; auto.
    }

    (* 2-2 *)
    assert (G2_2 : forall g, G.s al_h <= g -> generated (G.n al_h) g <> G.n a).
    {
      rewrite Heqal_h.
      simpl.
      intros g le c.
      apply H2 in le.
      apply le.
      left; symmetry; auto.
    }

    (* 2-3 *)
    assert (G2_3 : forall g, G.s al_h <= g -> ~ In (generated (G.n al_h) g) (map G.n ar)).
    {
      rewrite Heqal_h.
      simpl.
      intros g le c.
      apply H2 in le.
      apply le.
      right; rewrite map_app.
      apply in_app_iff.
      right; auto.
    }

    (* 3-1 *)
    assert (G3_1 : Forall (fun a' =>
                             G.pgprop al_h (fun p g => match a' with
                                                         | actor_state na' _ _ ga' =>
                                                           p = na' -> g < ga'
                                                       end)
                          ) al_t).
    {
      rewrite Heqal_h.
      simpl.
      auto.
    }

    (* 3-2 *)
    assert (G3_2 : G.pgprop al_h (fun p g => match a with
                                               | actor_state na _ _ ga =>
                                                 p = na -> g < ga
                                             end)).
    {
      rewrite Heqal_h.
      simpl.
      auto.
    }

    (* 3-3 *)
    assert (G3_3 : Forall (fun a' =>
                             G.pgprop al_h (fun p g => match a' with
                                                         | actor_state na' _ _ ga' =>
                                                           p = na' -> g < ga'
                                                       end)
                          ) ar).
    {
      rewrite Heqal_h.
      simpl.
      auto.
    }

    (* 合体 *)
    rewrite Heqal_h in *.
    simpl in *.
    constructor.
    + apply G1.
    + intros g le.
      rewrite app_cons.
      repeat (rewrite map_app).
      simpl.
      apply NotIn_app_iff.
      split; [ apply G2_1; auto | ].
      apply NotIn_cons_iff.
      split; [ apply G2_2; auto | apply G2_3; auto ].
    + apply Forall_app_iff.
      split; [ apply G3_1 | ].
      apply Forall_cons_iff.
      split; [ apply G3_2 | apply G3_3 ].
Qed.

Lemma gen_fresh_app_comm :
  forall actors_l actors_r,
    gen_fresh (actors_l ++ actors_r) ->
    gen_fresh (actors_r ++ actors_l).
Proof.
  induction actors_l.
  - intros actors_r H.
    rewrite app_nil_r.
    auto.
  - intros actors_r H.
    simpl in H.
    apply gen_fresh_insert in H.
    apply IHactors_l in H.
    simpl in H.
    apply gen_fresh_insert in H; auto.
Qed.

Lemma gen_fresh_insert_iff :
  forall a al ar,
    gen_fresh (a :: al ++ ar) <->
    gen_fresh (al ++ a :: ar).
Proof.
  intros a al ar.
  split.
  - apply gen_fresh_insert.
  - intros H.
    apply gen_fresh_app_comm in H.
    simpl in H.
    inversion H.
    constructor.
    + apply gen_fresh_app_comm; auto.
    + intros g le .
      rewrite map_app in *.
      apply NotIn_app_iff.
      rewrite and_comm.
      apply NotIn_app_iff.
      apply H3; auto.
    + apply Forall_app_iff.
      rewrite and_comm.
      apply Forall_app_iff.
      auto.
Qed.

(* Section Fresh *)

Lemma fresh_if_gen_fresh :
  forall a al ar,
    gen_fresh (al ++ a :: ar) ->
    ~ In (generated (G.n a) (G.s a)) (map G.n (al ++ a :: ar)).
Proof.
  intros a al ar H.
  rewrite map_app.
  simpl.
  apply NotIn_app_iff.
  rewrite app_cons.
  apply gen_fresh_insert_iff in H.
  inversion H; subst; simpl in *.
  specialize (H3 gen_num).
  assert (gen_num <= gen_num); auto.
  apply H3 in H0.
  rewrite map_app in H0.
  apply NotIn_app_iff in H0.
  destruct H0 as [ Hl Hr ].
  split; auto.
  intro c.
  destruct c as [ c | c ]; [ | apply Hr; auto ].
  apply name_not_cycle in c; auto.
Qed.

(* いらない。new_trans_fresh に *)
Lemma new_actor_fresh :
  forall msgs actors actors' actor,
    gen_fresh actors ->
    trans New (conf msgs actors) (conf msgs (actor :: actors')) -> (* この部分が矛盾なら意味ないんだけど、trans New がこの形になることは証明できる *)
    ~ In (G.n actor) (map G.n actors).
Proof.
  intros msgs actors actors' actor.
  intros weak tr contra.
  inversion tr; subst.
  apply fresh_if_gen_fresh in weak.
  apply weak.
  simpl in *.
  auto.
Qed.

Lemma new_trans_fresh :
  forall msgs actors actors' actor,
    gen_fresh actors ->
    trans New (conf msgs actors) (conf msgs (actor :: actors')) ->
    ~ In (G.n actor) (map G.n actors').
Proof.
  intros msgs actors actors' actor.
  intros fr tr.
  inversion tr; subst.
  apply fresh_if_gen_fresh in fr.
  rewrite map_app in *.
  simpl in *.
  auto.
Qed.

Lemma nss_eq_ns : forall actors actors',
                    map G.ns actors = map G.ns actors' ->
                    map G.n actors = map G.n actors'.
Proof.
  induction actors; intros actors' H.
  - simpl in *.
    symmetry in H.
    apply map_eq_nil in H.
    rewrite H; auto.
  - simpl in *.
    induction actors'.
    + simpl in H.
      inversion H.
    + simpl in *.
      inversion H; subst.
      destruct a, a0; simpl in *; subst.
      inversion H1; subst.
      f_equal.
      apply IHactors; auto.
Qed.

Lemma nss_eq_ss : forall actors actors',
                    map G.ns actors = map G.ns actors' ->
                    map G.s actors = map G.s actors'.
Proof.
  induction actors; intros actors' H.
  - simpl in *.
    symmetry in H.
    apply map_eq_nil in H.
    rewrite H; auto.
  - simpl in *.
    induction actors'.
    + simpl in H.
      inversion H.
    + simpl in *.
      inversion H; subst.
      destruct a, a0; simpl in *; subst.
      inversion H1; subst.
      f_equal.
      apply IHactors; auto.
Qed.

Lemma gen_fresh_related_only_name_number :
  forall actors actors',
    map G.ns actors = map G.ns actors' ->
    gen_fresh actors ->
    gen_fresh actors'.
Proof.
  intros actors actors'.
  revert actors.
  induction actors'; intros actors Heq H; auto.
  induction actors; simpl in *; [ inversion Heq | ].
  destruct a, a0; simpl in *.
  inversion Heq; subst.

  inversion H; subst.
  constructor.
  - apply (IHactors' actors); auto.
  - apply nss_eq_ns in H3.
    rewrite <- H3.
    auto.
  - clear IHactors' IHactors Heq H H4 H7.
    generalize dependent actors.
    induction actors'; intros actors Heq H; auto.
    destruct actors; simpl in *; inversion Heq; subst.
    destruct a1, a2; simpl in *.
    inversion H1; subst.
    inversion H; subst.
    constructor; auto.
    apply (IHactors' actors); auto.
Qed.

Lemma gen_fresh_increase :
  forall al ar n a b s,
    gen_fresh (al ++ (actor_state n a b s) :: ar) ->
    gen_fresh (al ++ (actor_state n a b (S s)) :: ar).
Proof.
  intros al ar n a b s H.
  apply gen_fresh_insert_iff.
  apply gen_fresh_insert_iff in H.
  inversion H; subst.
  constructor; auto.
  intros yet le.
  apply Le.le_Sn_le in le.
  auto.
Qed.
