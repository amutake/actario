Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.eqtype Ssreflect.ssrbool Ssreflect.seq.
Require Import syntax.

Section Label.
  Inductive label :=
  | Receive (to : name) (from : name) (content : message) (* `to` receives a message `content` from `from` *)
  | Send (from : name) (to : name) (content : message)    (* `from` sends a message `content` to `to` *)
  | New (parent : name) (child : name)                    (* `parent` creates an actor named `child` *)
  | Self (me : name).                                     (* `me` gets own name *)

  Definition eqlabel (l1 l2 : label) : bool :=
    match l1, l2 with
      | Receive t1 f1 c1, Receive t2 f2 c2 =>
        (t1 == t2) && (f1 == f2) && (c1 == c2)
      | Send f1 t1 c1, Send f2 t2 c2 =>
        (f1 == f2) && (t1 == t2) && (c1 == c2)
      | New p1 c1, New p2 c2 =>
        (p1 == p2) && (c1 == c2)
      | Self m1, Self m2 => m1 == m2
      | _, _ => false
    end.

  Lemma eqlabelP : Equality.axiom eqlabel.
  Proof.
    case=> [t1 f1 c1|f1 t1 c1|p1 c1|m1] [t2 f2 c2|f2 t2 c2|p2 c2|m2];
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
    - apply: (iffP andP).
      + by case; do 2 move/eqP=> <-.
      + case=> <- <-.
        split; exact: eqxx.
    - apply: (iffP eqP).
      + by move=><-.
      + by case=><-.
  Qed.

  Canonical label_eqMixin := EqMixin eqlabelP.
  Canonical label_eqType := Eval hnf in EqType label label_eqMixin.
End Label.

Reserved Notation "c1 '~(' t ')~>' c2" (at level 70).

(* transition defined as a relation of two config with label *)
(* trans label conf conf': label という遷移のラベルで conf が遷移して conf' になる *)
Inductive trans : label -> config -> config -> Prop :=
(* basic receive transition *)
| trans_receive :
    forall to from content f gen,
      (mkConfig [:: mkSending to from content]
                [:: mkActor to (become (receive f)) gen])
        ~(Receive to from content)~>
        (mkConfig [::]
                  [:: mkActor to (f content) gen])
(* basic send transition *)
| trans_send :
    forall from to content actions gen,
      (mkConfig [::]
                [:: mkActor from (send to content actions) gen])
        ~(Send from to content)~>
        (mkConfig [:: mkSending to from content]
                  [:: mkActor from actions gen])
(* basic new transition *)
| trans_new :
    forall parent behv cont gen,
      (mkConfig [::]
                [:: mkActor parent (new behv cont) gen])
        ~(New parent (generated gen parent))~>
        (mkConfig [::]
                  [:: (mkActor (generated gen parent) (become behv) 0);
                    (mkActor parent (cont (generated gen parent)) (S gen))])
(* basic self transition *)
| trans_self :
    forall me cont gen,
      (mkConfig [::]
                [:: mkActor me (self cont) gen])
        ~(Self me)~>
        (mkConfig [::]
                  [:: mkActor me (cont me) gen])
| trans_more_messages :
    forall messages actors messages' actors' label messages_l messages_r,
      mkConfig messages actors ~(label)~> mkConfig messages' actors' ->
      mkConfig (messages_l ++ messages ++ messages_r) actors
          ~(label)~>
        mkConfig (messages_l ++ messages' ++ messages_r) actors'
| trans_more_actors :
    forall messages actors messages' actors' label actors_l actors_r,
      mkConfig messages actors ~(label)~> mkConfig messages' actors' ->
      mkConfig messages (actors_l ++ actors ++ actors_r)
          ~(label)~>
        mkConfig messages' (actors_l ++ actors' ++ actors_r)
where "c1 '~(' t ')~>' c2" := (trans t c1 c2).

Hint Constructors trans.

Reserved Notation "c1 '~>*' c2" (at level 70).

Inductive trans_star : config -> config -> Prop :=
| trans_refl : forall c, c ~>* c
| trans_trans : forall c1 c2 c3, (exists label, c1 ~(label)~> c2) -> c2 ~>* c3 -> c1 ~>* c3
where "c1 '~>*' c2" := (trans_star c1 c2).

Hint Constructors trans_star.
