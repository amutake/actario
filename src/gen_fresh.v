Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.seq Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat.
Require Import Coq.Program.Equality Coq.Bool.Bool.
Require Coq.Lists.List.
Require Import util syntax semantics name_dec chain.

Definition name_next (a : actor) := (actor_name a, next_num a).

(**
 * アクターのリストに、以下の様なアクターはいない
 * 1. そのリストに現れる任意のアクターについて、そのアクターの生成番号的にまだ生成していないはずの名前を持つアクターは、そのリストには現れない
 *
 * つまり、これが成り立っていれば必ず fresh なアクターを生成できる
 *)
Inductive gen_fresh : seq actor -> Prop :=
| gen_fresh_nil : gen_fresh [::]
| gen_fresh_cons :
    forall actors name actions gen_num,
      gen_fresh actors ->
      (* 1. 先頭に追加するやつの、生成番号的にまだ生成していないはずの名前は、これまでに出てきていない *)
      (forall yet_num, gen_num <= yet_num -> generated yet_num name \notin map actor_name actors) ->
      (* 2. 先頭に追加するやつは、これまででてきたどのアクターについても、生成番号的にまだ生成していないはずのアクターではない *)
      all (fun nn =>
                match name with
                  | toplevel _ => true
                  | generated generated_num parent =>
                    (parent == nn.1) ==> (* そのアクターが親ならば、 *)
                    (generated_num < nn.2) (* 必ずそのアクターが以前に生成したもの *)
                end) (map name_next actors) ->
      gen_fresh (Build_actor name actions gen_num :: actors).

Hint Constructors gen_fresh.

Definition next_child (a : actor) := generated (next_num a) (actor_name a).

Theorem gen_fresh_soundness :
  forall actors,
    gen_fresh actors ->
    all (fun nn => generated nn.2 nn.1 \notin (map actor_name actors)) (map name_next actors).
Proof.
  elim.
  - move=> fr; done.
  - move=> a l IH fr.
    apply/allP=> prod H.
    inversion fr; subst.
    move/IH: H2=> H2.
    simpl.
    rewrite in_cons; apply/negP; move/orP.
    case.
    + move/eqP=> name_eq.
      rewrite -name_eq in H4.
      move/allP: H4.
      move: H => /=.
      rewrite in_cons.
      case/orP.
      * rewrite/name_next; move/eqP=> /= prod_eq.
        rewrite prod_eq in name_eq; simpl in name_eq.
        by symmetry in name_eq; apply name_not_cycle in name_eq.
      * move=> prod_in.
        move=> H.
        move/H/implyP: prod_in.
        move=> H1.
        rewrite eq_refl ltnn in H1.
        by move/H1: is_true_true.
    + move=> contra.
      move: H => /=.
      rewrite in_cons.
      case/orP.
      * move/eqP.
        rewrite/name_next => /= prod_eq.
        move: contra; rewrite prod_eq => /=.
        move/(_ gen_num): H3=> H3.
        have: gen_num <= gen_num by exact: leqnn.
        move/H3.
        move=> notin_p in_p.
        move/negP: notin_p=> notin_p.
        by apply: notin_p.
      * move=> in_p.
        move/allP/(_ prod): H2=> H2.
        by move/H2/negP: in_p=> in_p; apply: in_p.
Qed.

(* `name_next`, `name_next_eq_name` and `map_nil` are only used in gen_fresh_decided_by_only_name_and_next_number *)
Lemma name_next_eq_name : forall actors actors',
                    map name_next actors = map name_next actors' ->
                    map actor_name actors = map actor_name actors'.
Proof.
  elim; case.
  - done.
  - move=> a l H; inversion H.
  - move=> n actions next l IH.
    case.
    + move=> H.
      inversion H.
    + move=> a' l'.
      rewrite/name_next /=.
      case=> <- numeq lleq.
      congr (_ :: _).
      apply: IH.
      exact lleq.
Qed.

Lemma map_nil : forall (A B : Type) (f : A -> B) s,
                  map f s = [::] <-> s = [::].
Proof.
  move=> A B f s.
  split.
  - case: s.
    + done.
    + move=> a s /= H.
      inversion H.
  - by move=> ->.
Qed.

Lemma gen_fresh_decided_by_only_name_and_next_number :
  forall actors actors',
    map name_next actors = map name_next actors' ->
    gen_fresh actors ->
    gen_fresh actors'.
Proof.
  elim.
  - move=> actors' Heq H.
    move: Heq=> /=.
    by move=> Heq; symmetry in Heq; move/map_nil: Heq => ->.
  - case=> name1 actions1 next1 l IH actors'.
    elim: actors'.
    + move=> /= contra.
      inversion contra.
    + case=> name2 actions2 next2 l' IH' Heq H.
      simpl in *.
      case: Heq=> Heqa Heqn Heql.
      constructor.
      * apply: IH; [ done | inversion H; done ].
      * move/name_next_eq_name: Heql.
        move: Heqa Heqn=><-<-<-.
        by inversion H.
      * inversion H; subst.
        clear actions1 actions2 next2 H3 IH IH' H H5.
        move: l Heql H6.
        case: name2.
        - move=> addr l Heq Halll.
          clear addr l Heq Halll.
          elim: l'; [ done | ].
          by move=> a l H /=.
        - elim: l'.
          + done.
          + move=> a l IH gen parent l'.
            case: l'.
            * move=> contra; inversion contra.
            * move=> a' l' Heq Hall.
              case: Heq=> Heqname Heqnext Heqll.
              move: IH; move/(_ gen parent l' Heqll) => IH.
              move: Hall => /=.
              move/andP; case.
              move: Heqname Heqnext.
              case: a=> n acts next; case: a' => n' acts' next'.
              move=> /= -> /= -> impl.
              move/IH=> H.
              apply/andP.
              by split.
Qed.

(* weak trans invariant property (app -> and) *)
Lemma gen_fresh_app_and :
  forall actors_l actors_r,
    gen_fresh (actors_l ++ actors_r) ->
    gen_fresh actors_l /\ gen_fresh actors_r.
Proof.
  elim.
  - move=> actors_r /= H.
    by split.
  - move=> /= a actors_l IH actors_r H.
    inversion H; subst.
    case/IH: H2=> fr_l fr_r.
    split; last done.
    constructor; first done.
    + move=> yet_num; move/H3; rewrite map_cat mem_cat; move/orP=> notin_p.
      apply/negP=> in_p.
      apply: notin_p; by left.
    + move: H4; rewrite map_cat all_cat; case/andP=> all_l all_r.
      done.
Qed.

Lemma gen_fresh_swap_head :
  forall actor1 actor2 actors,
    gen_fresh (actor1 :: actor2 :: actors) ->
    gen_fresh (actor2 :: actor1 :: actors).
Proof.
  move=> a1 a2 actors H.
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

  remember (Build_actor name_a1 actions snum_a1) as a1.
  remember (Build_actor name_a2 actions0 snum_a2) as a2.

  (* 1-1 *)
  have G1_1 : gen_fresh actors; first done.

  (* 1-2 *)
  have G1_2 : forall g, snum_a1 <= g -> (generated g name_a1) \notin (map actor_name actors).
  {
    move=> g; move/H2.
    move/negP => notin_p.
    by apply/negP=> in_p; apply: notin_p; rewrite/= in_cons; apply/orP; right.
  }

  (* 1-3 *)
  have G1_3 : all (fun nn => if name_a1 is generated g p then
                               (p == nn.1) ==> (g < nn.2)
                             else
                               true)
                  (map name_next actors).
  {
    by move: H3 => /=; case/andP=> name_a1_p H3.
  }

  (* 2 *)
  have G2 : forall g, snum_a2 <= g ->
                      (generated g name_a2 != name_a1) &&
                      ((generated g name_a2) \notin (map actor_name actors)).
  {
    move=> g le.
    apply/andP; split.
    (* H3 を使う *)
    - move: H3 =>/=; case/andP.
      case eq_name_a1 : (name_a1) => [ | g_a1 p_a1 ].
      + move=> _ _; apply/negP; move/eqP=> contra; inversion contra.
      + move/implyP.
        rewrite Heqa2 =>/= imp all_p.
        apply/negP; case/eqP=> eq_g eq_n.
        subst.
        rewrite eq_refl in imp; move/imp: is_true_true.
        rewrite ltnNge; move/negP=> contra; by apply: contra.
    (* H1_2 を使う *)
    - apply/negP=> contra.
      move/H1_2: le.
      by move/negP=> contra'.
  }

  (* 3 *)
  have G3 : (if name_a2 is generated g p then
               ((p == name_a1) ==> (g < snum_a1))
             else true) &&
            (all (fun nn => if name_a2 is generated g p then
                             (p == nn.1) ==> (g < nn.2)
                           else
                             true) (map name_next actors)).
  {
    apply/andP; split.
    (* H2 *)
    - case eq_name_a2 : (name_a2) => [ | g_a2 p_a2 ]; first done.
      apply/implyP; move/eqP=> peq.
      rewrite ltnNge; apply/negP; move/H2.
      rewrite -peq -eq_name_a2 in_cons; move/orP=> tmp; apply: tmp.
      by left; subst.
    (* H1_3 *)
    - case eq_name_a2 : (name_a2) => [ ? | g_a2 p_a2 ].
      + exact: all_predT.
      + move: H1_3.
        by rewrite eq_name_a2.
  }

  (* combine *)
  subst; simpl in *.
  constructor.
  - constructor.
    + exact: G1_1.
    + exact: G1_2.
    + exact: G1_3.
  - move=> g; case/G2/andP => not_eq notin.
    apply/negP; case/orP; by apply/negP.
  - simpl; exact: G3.
Qed.

Lemma gen_fresh_insert :
  forall actor actors_l actors_r,
    gen_fresh (actor :: (actors_l ++ actors_r)) ->
    gen_fresh (actors_l ++ actor :: actors_r).
Proof.
  move=> a al.
  elim: al; first by move=> ? /= H.
  move=> al_hd al_tl IH ar H.
  move: H => /=; move/gen_fresh_swap_head => H.
  inversion H as [ | actors name actions gen_num H0 H1 H2 H3 ].
  constructor.
  - by apply: IH.
  - move=> g.
    move/H2.
    simpl.
    rewrite in_cons.
    case/norP.
    move=> a_neq.
    rewrite map_cat mem_cat.
    case/norP=> al_notin ar_notin.
    rewrite map_cat mem_cat.
    apply/norP; split; first done.
    simpl; rewrite in_cons; apply/norP; split; done.
  - move: H4.
    simpl.
    rewrite map_cat all_cat.
    case/and3P=> n_case all_al all_ar.
    rewrite map_cat all_cat.
    simpl.
    apply/and3P.
    by do !split.
Qed.

Lemma gen_fresh_app_comm :
  forall actors_l actors_r,
    gen_fresh (actors_l ++ actors_r) ->
    gen_fresh (actors_r ++ actors_l).
Proof.
  elim.
  - move=> ? ?; by rewrite cats0.
  - move=> al_hd al_tl IH ar H.
    move: H =>/=.
    move/gen_fresh_insert/IH =>/=.
    by move/gen_fresh_insert.
Qed.

Lemma gen_fresh_insert_iff :
  forall a al ar,
    gen_fresh (a :: al ++ ar) <->
    gen_fresh (al ++ a :: ar).
Proof.
  move=> a al ar.
  split.
  - apply/gen_fresh_insert.
  - move/gen_fresh_app_comm => /= H.
    inversion H.
    constructor.
    + by apply/gen_fresh_app_comm.
    + move=> yet le_num.
       rewrite map_cat mem_cat orb_comm -mem_cat -map_cat.
        by apply: H3.
    + by rewrite map_cat all_cat andb_comm -all_cat -map_cat.
Qed.

(* Section Fresh *)

Lemma fresh_if_gen_fresh :
  forall a al ar,
    gen_fresh (al ++ a :: ar) ->
    generated (next_num a) (actor_name a) \notin map actor_name (al ++ a :: ar).
Proof.
  move=> a al ar H.
  move/gen_fresh_insert_iff: H => H.
  inversion H; subst; simpl in *.

  rewrite map_cat => /=.
  rewrite mem_cat.
  rewrite in_cons.

  have gen_num_lerefl : gen_num <= gen_num.
    by exact: leqnn.
  move/H3: gen_num_lerefl.

  have cycle_name_false : generated gen_num name == name = false.
    rewrite eq_sym;  apply: negbTE; exact: name_neg_cycle.

  rewrite cycle_name_false.

  have orb_mid_false : forall a b, ~~ (a || b) -> ~~ [|| a, false | b].
    by case; case; simpl.
  move=> P; apply: orb_mid_false.

  by move: P; rewrite map_cat mem_cat.
Qed.

Lemma new_trans_fresh :
  forall sendings actors actors' actor,
    gen_fresh actors ->
    sendings >< actors ~(New (actor_name actor))~> sendings >< (actor :: actors') ->
    actor_name actor \notin map actor_name actors'.
Proof.
  move=> sendings actors actors' actor fr tr.
  inversion tr; subst; move: fr.
  move/fresh_if_gen_fresh.
  by do 2 (rewrite map_cat); move=> /=.
Qed.

Lemma gen_fresh_increase :
  forall actors_l actors_r name actions next,
    gen_fresh (actors_l ++ (Build_actor name actions next) :: actors_r) ->
    gen_fresh (actors_l ++ (Build_actor name actions (S next)) :: actors_r).
Proof.
  move=> actors_l actors_r name actions next H.
  apply/gen_fresh_insert_iff.
  move/gen_fresh_insert_iff: H.
  move=> H; inversion H; subst.
  constructor; [ done | | done ].
  move=> yet.
  move/ltnW.
  by move: yet.
Qed.
