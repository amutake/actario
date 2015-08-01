Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.eqtype Ssreflect.ssrbool Ssreflect.seq Ssreflect.ssrnat.
Require Import syntax semantics util no_dup.

(* applpi 形式の Transition Path (: nat -> option config) を導入するなら、下の定理が必要。
 * なぜかというと、TP n と TP (S n) の間について、別なラベルで遷移できてしまうなら、
 * label 情報を持っておらず前後の config 情報でラベルを判断する TP では、
 * そのラベルで遷移したことを表す述語、例えば eventually processed が意味をなさなくなってしまうから。
 *)
Section LabelUnique.

  Section Receive.
    Lemma receive_label_unique :
      forall c c' to fr co to' fr' co',
        no_dup (actors c) ->
        c ~(Receive to fr co)~> c' ->
        c ~(Receive to' fr' co')~> c' ->
        (to == to') && (fr == fr') && (co == co').
    Admitted.
  End Receive.

  Section Send.
    Lemma send_label_unique :
      forall c c' fr to co fr' to' co',
        no_dup (actors c) ->
        c ~(Send fr to co)~> c' ->
        c ~(Send fr' to' co')~> c' ->
        (fr == fr') && (to == to') && (co == co').
    Admitted.
  End Send.

  Section New.
    Lemma new_label_unique :
      forall c c' ch ch',
        no_dup (actors c) ->
        c ~(New ch)~> c' ->
        c ~(New ch')~> c' ->
        ch == ch'.
    Admitted.
  End New.

  Section Self.
    Lemma self_label_unique :
      forall c c' me me',
        no_dup (actors c) ->
        c ~(Self me)~> c' ->
        c ~(Self me')~> c' ->
        me == me'.
    Admitted.
  End Self.

  Theorem label_unique :
    forall c c' l1 l2,
      no_dup (actors c) ->
      c ~(l1)~> c' ->
      c ~(l2)~> c' ->
      l1 == l2.
  Proof.
    move=> c c'.
    case=> [ to fr co | fr to co | ch | me ];
      case=> [ to' fr' co' | fr' to' co' | ch' | me' ];
      move=> no tr1 tr2.
    - apply: (receive_label_unique no tr1 tr2).
    - inversion tr1; inversion tr2.
      subst.



  Lemma send_increments_sendings_size :
    forall c c' l,
      (if l is Send _ _ _ then true else false) ->
      c ~(l)~> c' ->
      (size (sending_messages c)).+1 == size (sending_messages c').
  Proof.
    move=> c c' l.
    case: l => [ ? ? ? // | fr to co _ | ? // | ? // ].
    move=> H.
    inversion H.
    simpl.
    repeat (rewrite size_cat).
    simpl.
      by rewrite addnS.
  Qed.

  Lemma receive_decrements_sendings_size :
    forall c c' l,
      (if l is Receive _ _ _ then true else false) ->
      c ~(l)~> c' ->
      size (sending_messages c) == (size (sending_messages c')).+1.
  Proof.
    move=> c c' l.
    case: l => [ to fr co _ | ? ? ? // | ? // | ? // ].
    move=> H; inversion H => /=.
    repeat (rewrite size_cat) => /=.
      by rewrite addnS.
  Qed.

  Lemma new_not_change_sendings_size :
    forall c c' l,
      (if l is New _ then true else false) ->
      c ~(l)~> c' ->
      size (sending_messages c) == size (sending_messages c').
  Proof.
    move=> c c' l.
    case: l => [ // | // | ch _ H | // ].
      by inversion H => /=.
  Qed.

  Lemma self_not_change_sendings_size :
    forall c c' l,
      (if l is Self _ then true else false) ->
      c ~(l)~> c' ->
      size (sending_messages c) == size (sending_messages c').
  Proof.
    move=> c c' l.
    case: l => [ // | // | // | me _ H ].
      by inversion H => /=.
  Qed.

  Lemma decrements_sendings_size_receive :
    forall c c' l,
      c ~(l)~> c' ->
      size (sending_messages c) == (size (sending_messages c')).+1 ->
      (if l is Receive _ _ _ then true else false).
  Proof.
    have tt : true = true by reflexivity.
    move=> c c' l tr.
    case eq_l : l => [ to fr co | fr to co | ch | me ] s.
    - done.
    - move/send_increments_sendings_size: tr.
      rewrite eq_l.
      move/(_ tt)/eqP=> H.
      move/eqP: s.
      rewrite -H; move/eqP=> contra.
      have add2 : forall n, n < n.+2 by exact: leqnSn.
      exfalso.
      move: contra; apply/negP/negbT.
        by apply: ltn_eqF.
    - move/new_not_change_sendings_size: tr.
      rewrite eq_l.
      move/(_ tt)/eqP=> H.
      move/eqP: s; rewrite H; move/eqP=> contra.
      exfalso.
      move: contra; apply/negP/negbT.
        by apply: ltn_eqF.
    - move/self_not_change_sendings_size: tr.
      rewrite eq_l.
      move/(_ tt)/eqP=> H.
      move/eqP: s; rewrite H; move/eqP=> contra.
      exfalso.
      move: contra; apply/negP/negbT.
        by apply: ltn_eqF.
  Qed.

  Lemma receive_label_sendings_count :
    forall sendings sendings' actors actors' to fr co,
      sendings >< actors ~(Receive to fr co)~> sendings' >< actors' ->
      count (fun s => s == Build_sending to fr co) sendings == (count (fun s => s == Build_sending to fr co) sendings').+1.
  Proof.
    move=> s s' a a' to fr co tr.
    inversion tr; subst => /=; clear tr.
    repeat (rewrite count_cat /=).
    rewrite -addnS eqn_add2l.
    rewrite -add1n eqn_add2r.
    rewrite eqb1.
    exact: eq_refl.
  Qed.

  Lemma receive_label_sendings_count_2 :
    forall sendings sendings' actors actors' to fr co,
      sendings >< actors ~(Receive to fr co)~> sendings' >< actors' ->
      count (fun s => s != Build_sending to fr co) sendings == (count (fun s => s != Build_sending to fr co) sendings').
  Proof.
    move=> s s' a a' to fr co tr.
    inversion tr; subst => /=; clear tr.
    repeat (rewrite count_cat /=).
    rewrite eqn_add2l.
    rewrite -eqb0.
    have: (Build_sending to fr co == Build_sending to fr co) = true by exact: eq_refl.
    move=>->.
    rewrite/nat_of_bool.
    have: (1 == 0) = false
      by apply/negP; move/eqP => contra; inversion contra.
    move=>-> /=.
      by rewrite add0n.
  Qed.

  Lemma receive_label_sendings_count_3 :
    forall sendings sendings' actors actors' to fr co n,
      sendings >< actors ~(Receive to fr co)~> sendings' >< actors' ->
      n == find (fun s => (count (fun s' => s == s') sendings) == (count (fun s' => s == s') sendings').+1) sendings ->
      to = nth to (map sending_to sendings) n /\ fr = nth fr (map sending_from sendings) n /\ co = nth co (map sending_content sendings) n.
  Proof.
    move=> sendings sendings' actors actors' to fr co n tr.
    set tr as i; move: i.
    move/receive_label_sendings_count=> count1.
    set tr as i; move: i.
    move/receive_label_sendings_count_2=> count2.
    admit.
  Qed.

  Variable A : eqType.

  Lemma rem_cons : forall s (a a' : A),
                     s = a :: rem a' s ->
                     a == a'.
  Proof.
    move=> s.
    elim: s.
    - move=> a a' /= //.
    - move=> ha hl IH a a'.
      case=>->.
      case a_eq: (a == a').
      + done.
      + move/IH.
          by rewrite -a_eq.
  Qed.

  Lemma rcons_not_nil :
    forall s (a : A),
      rcons s a != [::].
  Proof.
    elim.
    - move=> a.
      rewrite -cats1.
      apply/negP.
      move/eqP=> //.
    - move=> hd tl IH a.
      rewrite -cats1.
      apply/negP.
      move/eqP.
      simpl=> //.
  Qed.

  Lemma rcons_inj :
    forall s s' (a a' : A),
      rcons s a == rcons s' a' ->
      (s == s') && (a == a').
  Proof.
    move=> s s' a a'.
    by rewrite eqseq_rcons.
  Qed.

  Lemma cat_inj : forall (sl sl' sr : seq A),
          (sl ++ sr == sl' ++ sr) = (sl == sl').
  Proof.
    move=> sl sl' sr.
    apply/idP/idP.
    - move/eqP.
      elim sr using last_ind.
      + by rewrite 2!cats0; move=>->.
      + move=> a l IH.
        rewrite -cats1.
        rewrite 2!catA.
        rewrite 2!cats1.
        move/eqP.
        rewrite eqseq_rcons.
        case/andP.
        by move/eqP/IH.
    - move/eqP=>->.
      exact: eq_refl.
  Qed.

  Lemma rem_cat_inl :
    forall sl sr (a : A),
      a \in sl ->
      rem a (sl ++ sr) == rem a sl ++ sr.
  Proof.
    move=> sl; elim: sl.
    - move=> sr a.
      rewrite in_nil=> //.
    - move=> hd_sl tl_sl IH sr a.
      rewrite in_cons; move/orP; case.
      + move/eqP=><- /=.
        have: (a == a = true) by exact: eq_refl.
        move=>->.
        exact: eq_refl.
      + move=>/= a_in_tl.
        case eq_a_hd : (hd_sl == a); first exact: eq_refl.
        simpl.
        apply/eqP.
        congr (_ :: _).
        move: a_in_tl.
        move/IH.
        by move/(_ sr)/eqP.
  Qed.

  Lemma cons_snoc_rot :
    forall l (a a' : A),
      (a :: l) == (l ++ [:: a']) ->
      all (fun e => e == a) l.
  Proof.
    elim.
    - by move=> a a' /=.
    - move=> hd tl IH a a'.
      move/eqP=> /=.
      case=> <-.
      move/eqP/IH.
      move=> all_p.
      by apply/andP; split; first exact: eq_refl.
  Qed.

  Lemma rem_nseq :
    forall (a : A) n,
      rem a (nseq n a) == nseq n.-1 a.
  Proof.
    move=> a n.
    rewrite/nseq/ncons.
    case: n.
    - done.
    - move=> n/=.
      have: (a == a = true) by exact: eq_refl.
      move=>->.
      done.
  Qed.

  Lemma nseq_rcons :
    forall n (a a' : A),
      nseq n.+1 a == rcons (nseq n a) a' ->
      a == a'.
  Proof.
    move=> n a a'.
    elim: n.
    - simpl.
      move/eqP=> []->.
      exact: eq_refl.
    - move=> n /= IH.
      simpl.
      move/eqP.
      case.
      by move/eqP.
  Qed.

  Lemma rem_cat :
    forall sl sr (a a' : A),
      sl ++ sr == rem a (sl ++ a' :: sr) ->
      a == a'.
  Proof.
    move=> sl sr a a'.
    case a_in_sl : (a \in sl).
    - set a_in_sl as i; move: i.
      move/rem_cat_inl.
      move/(_ (a' :: sr))/eqP=>->.
      rewrite -cat1s catA cat_inj.
      clear sr.
      move: a_in_sl.
      elim: sl=> /=.
      + move/eqP=> //.
      + move=> hd tl IH a_in_sl H.
        case eq_hd_a : (hd == a).
        * move: H; rewrite eq_hd_a.
          move/cons_snoc_rot.
          move: a_in_sl.
          move/eqP: eq_hd_a=>-> a_in_sl.
          move/all_pred1P.
          move=> eq_tl.
          case eq_size : (size tl).
          -
          move: IH; rewrite eq_tl.
          move/(_ a (size tl))/eqP: rem_nseq=>->; apply.
          - case eq_size_tl : (size tl).
            + simpl.
  Admitted.


Lemma receive_remove :
  forall ss ss' acts acts' to fr co to' fr' co',
    ss' == rem (Build_sending to fr co) ss ->
    ss >< acts ~(Receive to' fr' co')~> ss' >< acts' ->
    to = to' /\ fr = fr' /\ co = co'.
Proof.
  move=> ss ss' acts acts' to fr co to' fr' co'.
  move/eqP=>-> H.
  inversion H; subst.
  clear H.




Lemma receive_label :
  forall s_l s_r to fr co to' fr' co' actors actors',
    ((s_l ++ Build_sending to fr co :: s_r) >< actors)
      ~(Receive to' fr' co')~> ((s_l ++ s_r) >< actors') ->
    to = to' /\ fr = fr' /\ co = co'.
Proof.
  move=> s_l s_r to fr co to' fr' co' actors actors'.
  move=> H; inversion H; subst.



Lemma message_received :
  forall sendings_l sendings_r to fr co actors actors' l,
  ((sendings_l ++ Build_sending to fr co :: sendings_r) >< actors)
    ~(l)~> ((sendings_l ++ sendings_r) >< actors') ->
  l == Receive to fr co.
Proof.
  move=> s_l s_r to fr co actors actors' l H.

  set H as i; move/decrements_sendings_size_receive: i=> /=.
  rewrite 2!size_cat.
  simpl.
  have H1: size s_l + (size s_r).+1 == (size s_l + size s_r).+1
    by rewrite addnS.
  move/(_ H1); clear H1.

  move: H; case: l => [ to' fr' co' H _ | // | // | // ].



  case eq_l : (l == Receive to fr co); first done.
  inversion H; subst.
  move/eqP: eq_l=> eq_l.




Require Import Coq.Program.Equality.
Theorem label_unique : forall c c' l1 l2,
                         no_dup (actors c) ->
                         c ~(l1)~> c' ->
                         c ~(l2)~> c' ->
                         l1 == l2.
Proof.

  (* move=> c c'. *)
  (* move=> [ to fr co | fr to co | ch | me ] [ to' fr' co' | fr' to' co' | ch' | me' ] tr1 tr2. *)
  (* - inversion tr1; inversion tr2; subst. *)
  (*   clear tr1 tr2. *)
  (*   inversion H9; inversion H8. *)
  (*   clear H8 H9. *)


  move=> c c' l1 l2 tr1.
  move: l2.
  case: tr1.
  - move=> to fr co f gen s_l s_r a_l a_r l2 tr2.
    inversion tr2.

    case: l2 => [to' fr' co'|? ? ?|?|?] tr2.
    dependent induction tr2 => //.
    + apply/eqP; congr (Receive _ _ _).
      * dependent induction IH. inversion IH; subst.


  move: l2.
  elim: tr1.
  - move=> to from content f gen sendings_l sendings_r actors_l actors_r.
    case=> [to' from' content'|? ? ?|?|?] tr2.
    dependent induction tr2 => //.
    + apply app3_nil in x.
      case: x => sl_nil x.
      case: x => s'_nil sr_nil.
      subst.
      move: x0 => /=.
      rewrite cats0.
      move=> s.
      specialize (IHtr2 to from content f gen).
      rewrite - s in IHtr2.
      remember (Build_actor to (become (receive f)) gen) as a.
      remember (Build_actor to (f content) gen) as a'.
      have IHeq1: sendings >< [:: a] = sendings >< [:: a]. done.
      have IHeq2: [::] >< [:: a'] = [::] >< [:: a']. done.
      move: IHeq1 IHeq2; apply: IHtr2.
    + move: IHtr2.
      move/(_ to from content f gen) => IHtr2.
      remember (Build_sending to from content) as s.
      have eq_a: actors = [:: Build_actor to (become (receive f)) gen].

      case
      f content = become (receive f) \/ f content <> become (receive f).
      remember (Build_actor to (become (receive f)) gen) as a.
      remember (Build_actor to (f content) gen) as a'.
      apply app3_single in x0.
      apply app3_single in x.

      case: x0; case; case=> eqal; case=> eqa eqar;
        case: x; case; case=> eqal'; case=> eqa' eqar';
        move: eqal eqar eqal' eqar'; move=> -> -> eqal eqar;
        try done.
      * case: eqal => eq_a.
        subst.


      *

        apply app3_sub_single with (s2 := actors) (a := Build_actor to (become (receive f)) gen) in x.
        - case: x=> eqal; case=> eqa' x.
            by case: x=> eqa eqar.
        - case=> fdef.
          rewrite <- fdef in *.


    remember (Receive to' from' content') as tr2' in tr2.
    elim: tr2.

    dependent induction tr2.
    elim: tr2.
    inversion tr2; subst.
    + done.
    +


  elim: t1; [do 7 move=> ?|do 7 move=> ?|do 6 move=> ?|do 5 move=> ?];
  case=> [? ? ?|? ? ?|? ?|?] tr2; by inversion tr2.
Qed.
