Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrnat.
Require Import Coq.Sorting.Permutation.
Require Import syntax semantics util no_dup.

Section ActorPersistence.

  (* actors do not disappear *)
  Theorem actor_persistence :
    forall c c' l n,
      n \in map actor_name c ->
      c ~(l)~> c' ->
      n \in map actor_name c'.
  Proof.
    move=> c c' l n n_in_c tr.
    inversion tr; subst;
    apply/(perm_map_in (Permutation_sym H0));
    move/(perm_map_in H): n_in_c=>/=; try done.
    - repeat rewrite in_cons.
      move=> ans.
      by apply/orP; right.
  Qed.

End ActorPersistence.

Section MessagePersistence.

  Lemma name_queue_to_name :
    forall c n q,
      (n, q) \in [seq (actor_name i, queue i) | i <- c] ->
      n \in [seq actor_name i | i <- c].
  Proof.
    move=> c n q.
    elim: c=>//.
    move=> a l IH /=.
    rewrite in_cons; case/orP.
    - case/eqP=> ? ?; subst.
      by apply/orP; left.
    - move=> ans; by apply/orP; right; apply/IH.
  Qed.

  Lemma no_dup_name_queue :
    forall a c q,
      no_dup (a :: c) ->
      (actor_name a, q) \in [seq (actor_name i, queue i) | i <- (a :: c)] ->
      q == queue a.
  Proof.
    move=> a c q no H.
    move: no; rewrite/no_dup/=; case/andP=> a_notin no.
    move: H=>/=; rewrite in_cons; case/orP.
    - by case/eqP=> ?; subst.
    - move=> contra; exfalso; move/negP: a_notin; apply.
      move: contra; clear.
      apply/name_queue_to_name.
  Qed.

  Lemma same_name_queue :
    forall c c' n q q',
      no_dup c ->
      [seq (actor_name i, queue i) | i <- c] = [seq (actor_name i, queue i) | i <- c'] ->
      (n, q) \in [seq (actor_name i, queue i) | i <- c] ->
      (n, q') \in [seq (actor_name i, queue i) | i <- c'] ->
      q == q'.
  Proof.
    move=> c c' n q q' no <- nq_in nq_in'.
    move: no nq_in nq_in'; elim: c=>//.
    move=> a l IH.
    rewrite/no_dup/=; case/andP=> a_notin u.
    repeat rewrite in_cons.
    case/orP=> tmp; case/orP=> tmp'; move: tmp tmp'.
    - by case/eqP=> ? ?; case/eqP=> ? ?; subst.
    - by case/eqP=> ? ?; subst=> contra; exfalso; move/negP: a_notin; apply; apply/name_queue_to_name.
    - by move=> contra; case/eqP=> ? ?; subst; exfalso; move/negP: a_notin; apply; apply/name_queue_to_name.
    - by move=> ih ih'; apply/IH.
  Qed.

  Lemma receive_cons :
    forall c c' n q q' m,
      no_dup c ->
      no_dup c' ->
      (n, q) \in [seq (actor_name i, queue i) | i <- c] ->
      (n, q') \in [seq (actor_name i, queue i) | i <- c'] ->
      c ~(Receive n m)~> c' ->
      q == m :: q'.
  Proof.
    move=> c c' n q q' m.
    move=> no no' nq_in nq_in' tr.
    inversion tr; subst; clear tr.
    move/(perm_no_dup H1): no=> no.
    move/(perm_no_dup H4): no'=> no'.
    move/(perm_map_in H1): nq_in.
    move/(no_dup_name_queue no).
    move/(perm_map_in H4): nq_in'.
    move/(no_dup_name_queue no').
    by rewrite/=; move/eqP=>->; move/eqP=>->.
  Qed.

  Lemma not_receive :
    forall c c' n q q' m n',
      no_dup c ->
      no_dup c' ->
      (n, q) \in [seq (actor_name i, queue i) | i <- c] ->
      (n, q') \in [seq (actor_name i, queue i) | i <- c'] ->
      n != n' ->
      c ~(Receive n' m)~> c' ->
      q == q'.
  Proof.
    move=> c c' n q q' m n'.
    move=> no no' nq_in nq_in' neq tr.
    inversion tr; subst; clear tr.
    move/(perm_map_in H1): nq_in=>/=.
    rewrite in_cons; case/orP; first by case/eqP=> ? ?; subst; exfalso; move/negP: neq; apply.
    move/(perm_map_in H4): nq_in'=>/=.
    rewrite in_cons; case/orP; first by case/eqP=> ? ?; subst; exfalso; move/negP: neq; apply.

    move/(perm_no_dup H1): no.
    rewrite/no_dup/=; case/andP=> _; clear.

    elim: rest=>//.
    move=> a l IH /=.
    case/andP=> a_notin u.
    rewrite in_cons; case/orP.
    - case/eqP=> ? ?; subst.
      rewrite in_cons; case/orP.
      + by case/eqP=> ?; subst.
      + move=> contra; exfalso; move/negP: a_notin; apply.
        by apply/name_queue_to_name.
    - move=> contra; rewrite in_cons; case/orP.
      + case/eqP=> ? ?; subst.
        exfalso; move/negP: a_notin; apply.
        by apply/name_queue_to_name.
      + by move=> H; apply/IH.
  Qed.

  Lemma Permutation_swap :
    forall (A : Type) s (a b : A) rest,
      Permutation s (a :: b :: rest) ->
      Permutation s (b :: a :: rest).
  Proof.
    move=> A s a b rest perm.
    move/(_ _ [:: b] rest a): Permutation_middle=>/= swap.
    apply/(Permutation_trans perm swap).
  Qed.

  Lemma send_cons :
    forall c c' n q q' fr m,
      no_dup c ->
      no_dup c' ->
      (n, q) \in [seq (actor_name i, queue i) | i <- c] ->
      (n, q') \in [seq (actor_name i, queue i) | i <- c'] ->
      c ~(Send fr n m)~> c' ->
      q ++ [:: m] == q'.
  Proof.
    move=> c c' n q q' fr m.
    move=> no no' nq_in nq_in' tr.
    inversion tr; subst; clear tr.
    move/(perm_no_dup (Permutation_swap H4)): no=> no.
    move/(perm_no_dup (Permutation_swap H5)): no'=> no'.
    move/(perm_map_in (Permutation_swap H4)): nq_in.
    move/(no_dup_name_queue no).
    move/(perm_map_in (Permutation_swap H5)): nq_in'.
    move/(no_dup_name_queue no').
    by move/eqP=>->; move/eqP=>->/=.
  Qed.

  Lemma not_send :
    forall c c' n q q' fr n' m,
      no_dup c ->
      no_dup c' ->
      (n, q) \in [seq (actor_name i, queue i) | i <- c] ->
      (n, q') \in [seq (actor_name i, queue i) | i <- c'] ->
      n != n' ->
      c ~(Send fr n' m)~> c' ->
      q == q'.
  Proof.
    move=> c c' n q q' fr n' m.
    move=> no no' nq_in nq_in' neq tr.
    inversion tr; subst; clear tr.
    move/(perm_map_in (Permutation_swap H4)): nq_in=>/=.
    rewrite in_cons; case/orP; first by case/eqP=> ? ?; subst; exfalso; move/negP: neq; apply.
    move/(perm_map_in (Permutation_swap H5)): nq_in'=>/=.
    rewrite in_cons; case/orP; first by case/eqP=> ? ?; subst; exfalso; move/negP: neq; apply.

    move/(perm_no_dup (Permutation_swap H4)): no.
    rewrite/no_dup/=.
    case/andP=> _ no nq_in' nq_in.
    move: same_name_queue.
    move/(_ ({|
             state_type := from_st;
             actor_name := fr;
             remaining_actions := (n') ! m; from_cont;
             next_num := from_gen;
             behv := from_f;
             queue := from_msgs |} :: rest)
            ({|
             state_type := from_st;
             actor_name := fr;
             remaining_actions := from_cont;
             next_num := from_gen;
             behv := from_f;
             queue := from_msgs |} :: rest) n q q' no Logic.eq_refl nq_in nq_in').
    done.
  Qed.

  Lemma count_mem_app :
    forall (E : eqType) (e : E) s s',
      count_mem e (s ++ s') = count_mem e s + count_mem e s'.
  Proof.
    move=> E e; elim=>//.
    move=> a l IH s' /=.
      by rewrite IH addnA.
  Qed.

  (* messages do not disappear without received *)
  Theorem message_persistence :
    forall c c' l nm q q' m n,
      no_dup c ->
      no_dup c' ->
      (nm, q) \in [seq (actor_name i, queue i) | i <- c] ->
      count_mem m q == n ->
      c ~(l)~> c' ->
      (nm, q') \in [seq (actor_name i, queue i) | i <- c'] ->
      match l with
      | Receive to co =>
        if (to == nm) && (co == m) then
          count_mem m q' == n.-1
        else
          count_mem m q' == n
      | Send _ to co =>
        if (to == nm) && (co == m) then
          count_mem m q' == n.+1
        else
          count_mem m q' == n
      | _ => count_mem m q' == n
      end.
  Proof.
    move=> c c' l nm q q' m n.
    move=> no no' nq_in n_eq tr nq_in'.
    move: tr.
    case: l=> [ to co | fr to co | ch | me ]=> tr /=.
    - case to_nm_eq : (to == nm) => /=.
      + move/eqP: to_nm_eq=> ?; subst.
        move: receive_cons.
        move/(_ c c' nm q q' co no no' nq_in nq_in' tr).
        move/eqP=> ?; subst.
        move/eqP: n_eq=> ?; subst.
        case co_m_eq : (co == m) => /=.
        * move/eqP: co_m_eq=> ?; subst.
          by repeat rewrite eq_refl.
        * by rewrite co_m_eq.
      + move: not_receive.
        move/(_ c c' nm q q' co to no no' nq_in nq_in' _ tr).
        have neq' : (nm != to = true) by rewrite eq_sym to_nm_eq.
        rewrite neq' /=.
        by move/implyP=>/=/eqP=><-.
    - case to_nm_eq : (to == nm) => /=.
      + move/eqP: to_nm_eq=> ?; subst.
        move: send_cons.
        move/(_ c c' nm q q' fr co no no' nq_in nq_in' tr).
        move/eqP=> ?; subst.
        move/eqP: n_eq=> ?; subst.
        case co_m_eq : (co == m) => /=.
        * move/eqP: co_m_eq=> ?; subst.
          by rewrite count_mem_app /= eq_refl /= addn1.
        * by rewrite count_mem_app /= co_m_eq /= addn0 addn0.
      + move: not_send.
        move/(_ c c' nm q q' fr to co no no' nq_in nq_in' _ tr).
        have neq' : (nm != to = true) by rewrite eq_sym to_nm_eq.
        rewrite neq' /=.
        by move/implyP=>/=/eqP=><-.
    - inversion tr; subst; clear tr.
      have parent_H : ((nm == parent) || (nm \in (map actor_name rest))).
      move/(perm_map_in H0): nq_in=>/=.
      rewrite in_cons; case/orP.
      + by case/eqP=> ? ?; subst; apply/orP; left.
      + by move=> ans; apply/orP; right; apply/(name_queue_to_name ans).
      have child_H : ((generated gen parent != parent) && ((generated gen parent) \notin (map actor_name rest))).
      move/(perm_no_dup H1): no'; rewrite/no_dup/=.
      case/andP; move/negP=> ans _.
      apply/andP; split; apply/negP=> contra; apply/ans; rewrite in_cons; apply/orP;
                                      [ by left | by right ].
      have hoge : (nm == generated gen parent = false).
      case/andP: child_H=> not_parent nin_rest.
      apply/negP; move/eqP=> ?; subst.
      case/orP: parent_H.
      + by rewrite (negbTE not_parent).
      + by rewrite (negbTE nin_rest).
      move/(perm_no_dup H0): no=> no.
      move/(perm_map_in H0): nq_in=> nq_in.
      move: same_name_queue.
      move/(_ ({|
          state_type := parent_st;
          actor_name := parent;
          remaining_actions := (n) <- new child_behv with child_ini;
                               parent_cont n;
          next_num := gen;
          behv := parent_behv;
          queue := parent_msgs |} :: rest)
              ({|
             state_type := parent_st;
             actor_name := parent;
             remaining_actions := parent_cont (generated gen parent);
             next_num := gen.+1;
             behv := parent_behv;
             queue := parent_msgs |}
           :: rest) nm q q' no Logic.eq_refl nq_in _).
      move=> /= ans.
      have H : ((nm, q') \in (parent, parent_msgs) :: [seq (actor_name i, queue i) | i <- rest]).
      move/(perm_map_in H1): nq_in'=>/=.
      rewrite in_cons; case/orP.
      + case/eqP=> ? _; subst.
          by exfalso; move/negP: hoge; apply.
      + done.
        by move/(_ H): ans; move/eqP=> ?; subst.
    - inversion tr; subst; clear tr.
      move/(perm_no_dup H0): no=> no.
      move/(perm_map_in H0): nq_in=> nq_in.
      move/(perm_map_in H1): nq_in'=> nq_in'.
      move: same_name_queue.
      move/(_ ({|
          state_type := st;
          actor_name := me;
          remaining_actions := (me) <- self ; cont me;
          next_num := gen;
          behv := f;
          queue := msgs |} :: rest) ({|
          state_type := st;
          actor_name := me;
          remaining_actions := cont me;
          next_num := gen;
          behv := f;
          queue := msgs |} :: rest) nm q q' no Logic.eq_refl nq_in nq_in')=>/=.
      by move/eqP=><-.
  Qed.
End MessagePersistence.
