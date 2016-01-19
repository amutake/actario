Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Sorting.Permutation.
Require Import Ssreflect.eqtype Ssreflect.ssrbool Ssreflect.seq Ssreflect.ssrnat.
Require Import syntax.

Section Label.
  Inductive label :=
  | Receive (to : name) (msg : message) (* `to` receives a message `content` *)
  | Send (from : name) (to : name) (content : message)    (* `from` sends a message `msg` to `to` *)
  | New (child : name)                                    (* an actor named `child` is created *)
  | Self (me : name).                                     (* `me` gets own name *)

  Definition eqlabel (l1 l2 : label) : bool :=
    match l1, l2 with
      | Receive t1 c1, Receive t2 c2 =>
        (t1 == t2) && (c1 == c2)
      | Send f1 t1 c1, Send f2 t2 c2 =>
        (f1 == f2) && (t1 == t2) && (c1 == c2)
      | New c1, New c2 => c1 == c2
      | Self m1, Self m2 => m1 == m2
      | _, _ => false
    end.

  Lemma eqlabelP : Equality.axiom eqlabel.
  Proof.
    case=> [t1 c1|f1 t1 c1|c1|m1] [t2 c2|f2 t2 c2|c2|m2];
      try by constructor.
    - apply: (iffP andP).
      + by case=> []; do 2 move/eqP=> <-.
      + case=> <- <-.
        split; exact: eqxx.
    - apply: (iffP andP).
      + by case=> /andP []; do 3 move/eqP=> <-.
      + case=> <- <- <-.
        split; last exact: eqxx.
        pose H := (rwP andP); apply H.
        split; exact: eqxx.
    - apply: (iffP eqP).
      + by move=><-.
      + by case=><-.
    - apply: (iffP eqP).
      + by move=><-.
      + by case=><-.
  Qed.

  Canonical label_eqMixin := EqMixin eqlabelP.
  Canonical label_eqType := Eval hnf in EqType label label_eqMixin.
End Label.

(* labeled transition semantics *)
(* between two configurations with a label *)
Reserved Notation "c1 '~(' t ')~>' c2" (at level 60).
Inductive trans : label -> config -> config -> Prop :=
(* receive transition *)
| trans_receive :
    forall to msg
           st next_state f gen msgs
           rest actors actors',
      Permutation actors (
                    {|
                      state_type := st;
                      actor_name := to;
                      remaining_actions := become next_state;
                      next_num := gen;
                      behv := f;
                      queue := (msg :: msgs)
                    |} :: rest) ->
      Permutation actors' (
                    {|
                      actor_name := to;
                      remaining_actions := interp (f next_state) msg;
                      next_num := gen;
                      behv := f;
                      queue := msgs
                    |} :: rest) ->
      actors ~(Receive to msg)~> actors'
(* send transition *)
| trans_send :
    forall from to msg
           from_st from_cont from_gen from_msgs from_f
           to_st to_actions to_gen to_msgs to_f
           rest actors actors',
      Permutation actors (
                    {|
                      state_type := from_st;
                      actor_name := from;
                      remaining_actions := send to msg from_cont;
                      next_num := from_gen;
                      behv := from_f;
                      queue := from_msgs
                    |} :: {|
                      state_type := to_st;
                      actor_name := to;
                      remaining_actions := to_actions;
                      next_num := to_gen;
                      behv := to_f;
                      queue := to_msgs
                       |} :: rest) ->
      Permutation actors' (
                    {|
                      state_type := from_st;
                      actor_name := from;
                      remaining_actions := from_cont;
                      next_num := from_gen;
                      behv := from_f;
                      queue := from_msgs
                    |} :: {|
                         state_type := to_st;
                         actor_name := to;
                         remaining_actions := to_actions;
                         next_num := to_gen;
                         behv := to_f;
                         queue := to_msgs ++ [:: msg]
                       |} :: rest) ->
      actors ~(Send from to msg)~> actors'
(* new transition *)
| trans_new :
    forall parent_st parent parent_behv parent_cont gen parent_msgs
           child_st child_behv child_ini
           rest actors actors',
      Permutation actors (
                    {|
                      state_type := parent_st;
                      actor_name := parent;
                      remaining_actions := new child_behv child_ini parent_cont;
                      next_num := gen;
                      behv := parent_behv;
                      queue := parent_msgs
                    |} :: rest) ->
      Permutation actors' (
                    {|
                      state_type := child_st;
                      actor_name := generated gen parent;
                      remaining_actions := become child_ini;
                      next_num := 0;
                      behv := child_behv;
                      queue := [::]
                    |} ::
                    {|
                      state_type := parent_st;
                      actor_name := parent;
                      remaining_actions := parent_cont (generated gen parent);
                      next_num := S gen;
                      behv := parent_behv;
                      queue := parent_msgs
                    |} :: rest) ->
      actors ~(New (generated gen parent))~> actors'
(* self transition *)
| trans_self :
    forall st me cont gen f msgs
           rest actors actors',
      Permutation actors (
                    {|
                      state_type := st;
                      actor_name := me;
                      remaining_actions := self cont;
                      next_num := gen;
                      behv := f;
                      queue := msgs
                    |} :: rest) ->
      Permutation actors' (
                    {|
                      state_type := st;
                      actor_name := me;
                      remaining_actions := cont me;
                      next_num := gen;
                      behv := f;
                      queue := msgs
                    |} :: rest) ->
      actors ~(Self me)~> actors'
where "c1 '~(' t ')~>' c2" := (trans t c1 c2).

Hint Constructors trans.

Reserved Notation "c1 '~>*' c2" (at level 70).

Inductive trans_star : config -> config -> Prop :=
| trans_refl : forall c c',
    Permutation c c' ->
    c ~>* c'
| trans_trans : forall c1 c2 c3, (exists label, c1 ~(label)~> c2) -> c2 ~>* c3 -> c1 ~>* c3
where "c1 '~>*' c2" := (trans_star c1 c2).

Hint Constructors trans_star.

(* trans utils *)

Lemma trans_perm_l :
  forall c c' c'' l,
    Permutation c c' ->
    c ~(l)~> c'' ->
    c' ~(l)~> c''.
Proof.
  move=> c c' c''.
  case=> [ to msg | from to msg | child | me ];
    move/Permutation_sym=> perm H; inversion H; subst.
  - move: (Permutation_trans perm H2)=> perm'.
    eapply trans_receive; [ apply perm' | by [] ].
  - move: (Permutation_trans perm H5)=> perm'.
    eapply trans_send; [ apply perm' | by [] ].
  - move: (Permutation_trans perm H1)=> perm'.
    eapply trans_new; [ apply perm' | by [] ].
  - move: (Permutation_trans perm H1)=> perm'.
    eapply trans_self; [ apply perm' | by [] ].
Qed.

Lemma trans_perm_r :
  forall c c' c'' l,
    Permutation c' c'' ->
    c ~(l)~> c' ->
    c ~(l)~> c''.
Proof.
  move=> c c' c''.
  case=> [ to msg | from to msg | child | me ];
    move/Permutation_sym=> perm H; inversion H; subst.
  - move: (Permutation_trans perm H5)=> perm'.
    eapply trans_receive; [ apply H2 | apply perm' ].
  - move: (Permutation_trans perm H6)=> perm'.
    eapply trans_send; [ apply H5 | apply perm' ].
  - move: (Permutation_trans perm H2)=> perm'.
    eapply trans_new; [ apply H1 | apply perm' ].
  - move: (Permutation_trans perm H2)=> perm'.
    eapply trans_self; [ apply H1 | apply perm' ].
Qed.

Lemma trans_nil_l :
  forall c l, ~ ([::] ~(l)~> c).
Proof.
  move=> c l contra;
    inversion contra; subst;
    move: H;
    apply/Permutation_nil_cons.
Qed.

Lemma trans_nil_r :
  forall c l, ~ (c ~(l)~> [::]).
Proof.
  move=> c l contra;
    inversion contra; subst;
    move: H0;
    apply/Permutation_nil_cons.
Qed.
