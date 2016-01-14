Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Sorting.Permutation.
Require Import Ssreflect.eqtype Ssreflect.ssrbool Ssreflect.seq Ssreflect.ssrnat.
Require Import syntax.

Section Label.
  Inductive label :=
  | Receive (to : name) (from : name) (msg : message) (* `to` receives a message `content` from `from` *)
  | Send (from : name) (to : name) (content : message)    (* `from` sends a message `msg` to `to` *)
  | New (child : name)                                    (* an actor named `child` is created *)
  | Self (me : name).                                     (* `me` gets own name *)

  Definition eqlabel (l1 l2 : label) : bool :=
    match l1, l2 with
      | Receive t1 f1 c1, Receive t2 f2 c2 =>
        (t1 == t2) && (f1 == f2) && (c1 == c2)
      | Send f1 t1 c1, Send f2 t2 c2 =>
        (f1 == f2) && (t1 == t2) && (c1 == c2)
      | New c1, New c2 => c1 == c2
      | Self m1, Self m2 => m1 == m2
      | _, _ => false
    end.

  Lemma eqlabelP : Equality.axiom eqlabel.
  Proof.
    case=> [t1 f1 c1|f1 t1 c1|c1|m1] [t2 f2 c2|f2 t2 c2|c2|m2];
      try by constructor.
    - apply: (iffP andP).
      + by case=> /andP []; do 3 move/eqP=> <-.
      + case=> <- <- <-.
        split; last exact: eqxx.
        pose H := (rwP andP); apply H.
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
    forall to from msg next_state f gen msgs
           rest actors actors',
      Permutation actors (
                    {|
                      actor_name := to;
                      remaining_actions := become next_state;
                      next_num := gen;
                      behv := receive f;
                      queue := (msg :: msgs)
                    |} :: rest) ->
      Permutation actors' (
                    {|
                      actor_name := to;
                      remaining_actions := (f msg next_state);
                      next_num := gen;
                      behv := receive f;
                      queue := msgs
                    |} :: rest) ->
      actors ~(Receive to from msg)~> actors'
(* send transition *)
| trans_send :
    forall from to msg
           from_cont from_gen from_msgs from_f
           to_actions to_gen to_msgs to_f
           rest actors actors',
      Permutation actors (
                    {|
                      actor_name := from;
                      remaining_actions := send to msg from_cont;
                      next_num := from_gen;
                      behv := from_f;
                      queue := from_msgs
                    |} :: {|
                      actor_name := to;
                      remaining_actions := to_actions;
                      next_num := to_gen;
                      behv := to_f;
                      queue := to_msgs
                       |} :: rest) ->
      Permutation actors' (
                    {|
                      actor_name := from;
                      remaining_actions := from_cont;
                      next_num := from_gen;
                      behv := from_f;
                      queue := from_msgs
                    |} :: {|
                         actor_name := to;
                         remaining_actions := to_actions;
                         next_num := to_gen;
                         behv := to_f;
                         queue := to_msgs ++ [:: msg]
                       |} :: rest) ->
      actors ~(Send from to msg)~> actors'
(* new transition *)
| trans_new :
    forall parent parent_behv parent_cont gen parent_msgs
           child_behv
           rest actors actors',
      Permutation actors (
                    {|
                      actor_name := parent;
                      remaining_actions := new child_behv parent_cont;
                      next_num := gen;
                      behv := parent_behv;
                      queue := parent_msgs
                    |} :: rest) ->
      Permutation actors' (
                    {|
                      actor_name := parent;
                      remaining_actions := parent_cont (generated gen parent);
                      next_num := gen;
                      behv := parent_behv;
                      queue := parent_msgs
                    |} :: {|
                      actor_name := generated gen parent;
                      remaining_actions := become 0;
                      next_num := 0;
                      behv := child_behv;
                      queue := [::]
                    |} :: rest) ->
      actors ~(New (generated gen parent))~> actors'
(* self transition *)
| trans_self :
    forall me cont gen f msgs
           rest actors actors',
      Permutation actors (
                    {|
                      actor_name := me;
                      remaining_actions := self cont;
                      next_num := gen;
                      behv := f;
                      queue := msgs
                    |} :: rest) ->
      Permutation actors' (
                    {|
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
| trans_refl : forall c, c ~>* c
| trans_trans : forall c1 c2 c3, (exists label, c1 ~(label)~> c2) -> c2 ~>* c3 -> c1 ~>* c3
where "c1 '~>*' c2" := (trans_star c1 c2).

Hint Constructors trans_star.
