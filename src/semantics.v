Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.eqtype Ssreflect.ssrbool Ssreflect.seq Ssreflect.ssrnat.
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

(* labeled transition semantics *)
(* between two configurations with a label *)
Reserved Notation "c1 '~(' t ')~>' c2" (at level 60).
Inductive trans : label -> config -> config -> Prop :=
(* receive transition *)
| trans_receive :
    forall sendings_l sendings_r to from content f gen actors_l actors_r,
      (sendings_l ++ Build_sending to from content :: sendings_r) >< (actors_l ++ Build_actor to (become (receive f)) gen :: actors_r)
        ~(Receive to from content)~>
        (sendings_l ++ sendings_r) >< (actors_l ++ Build_actor to (f content) gen :: actors_r)
(* send transition *)
| trans_send :
    forall sendings_l sendings_r from to content cont gen actors_l actors_r,
      (sendings_l ++ sendings_r) >< (actors_l ++ Build_actor from (send to content cont) gen :: actors_r)
         ~(Send from to content)~>
         (sendings_l ++ Build_sending to from content :: sendings_r) >< (actors_r ++ Build_actor from cont gen :: actors_r)
(* new transition *)
| trans_new :
    forall sendings parent behv cont gen actors_l actors_r,
      sendings >< (actors_l ++ Build_actor parent (new behv cont) gen :: actors_r)
        ~(New parent (generated gen parent))~>
        sendings >< (Build_actor (generated gen parent) (become behv) 0 :: actors_l ++
                     Build_actor parent (cont (generated gen parent)) (S gen) :: actors_r)
(* self transition *)
| trans_self :
    forall sendings me cont gen actors_l actors_r,
      sendings >< (actors_l ++ Build_actor me (self cont) gen :: actors_r)
        ~(Self me)~>
        sendings >< (actors_l ++ Build_actor me (cont me) gen :: actors_r)
where "c1 '~(' t ')~>' c2" := (trans t c1 c2).

Hint Constructors trans.

Reserved Notation "c1 '~>*' c2" (at level 70).

Inductive trans_star : config -> config -> Prop :=
| trans_refl : forall c, c ~>* c
| trans_trans : forall c1 c2 c3, (exists label, c1 ~(label)~> c2) -> c2 ~>* c3 -> c1 ~>* c3
where "c1 '~>*' c2" := (trans_star c1 c2).

Hint Constructors trans_star.
