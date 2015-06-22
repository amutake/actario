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

Reserved Notation "c1 '~(' t ')~>' c2" (at level 90).

(* transition defined as a relation of two config with label *)
(* trans label conf conf': label という遷移のラベルで conf が遷移して conf' になる *)
Inductive trans : label -> config -> config -> Prop :=
(* receive transition *)
| trans_receive :
    forall sendings to from content f gen actors,
      [:: Build_sending to from content] \cup sendings >< [:: Build_actor to (become (receive f)) gen] \cup actors
        ~(Receive to from content)~>
        sendings >< [:: Build_actor to (f content) gen] \cup actors
(* send transition *)
| trans_send :
    forall sendings from to content cont gen actors,
      sendings >< [:: Build_actor from (send to content cont) gen] \cup actors
        ~(Send from to content)~>
        [:: Build_sending to from content] \cup sendings >< [:: Build_actor from cont gen] \cup actors
(* new transition *)
| trans_new :
    forall sendings parent behv cont gen actors,
      sendings >< [:: Build_actor parent (new behv cont) gen] \cup actors
        ~(New parent (generated gen parent))~>
        sendings ><
                  [:: Build_actor (generated gen parent) (become behv) 0
                   ; Build_actor parent (cont (generated gen parent)) (S gen)
                  ] \cup actors
(* self transition *)
| trans_self :
    forall sendings me cont gen actors,
      sendings >< [:: Build_actor me (self cont) gen] \cup actors
        ~(Self me)~>
        sendings >< [:: Build_actor me (cont me) gen] \cup actors
where "c1 '~(' t ')~>' c2" := (trans t c1 c2).

Hint Constructors trans.

Reserved Notation "c1 '~>*' c2" (at level 70).

Inductive trans_star : config -> config -> Prop :=
| trans_refl : forall c, c ~>* c
| trans_trans : forall c1 c2 c3, (exists label, c1 ~(label)~> c2) -> c2 ~>* c3 -> c1 ~>* c3
where "c1 '~>*' c2" := (trans_star c1 c2).

Hint Constructors trans_star.
