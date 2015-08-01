Set Implicit Arguments.
Unset Strict Implicit.

Require Import syntax semantics util.

(* the following definitions are refered to:
 * Reynald Affeldt and Naoki Kobayashi, A Coq library for verification of concurrent programs, Electronic Notes in Theoretical Computer Science, 199:17-32, 2008
 *)
Definition path := nat -> option config.

Definition is_transition_path (p : path) : Prop :=
  forall n,
    (forall c, p n = Some c ->
               (exists c' l, p (S n) = Some c' /\ c ~(l)~> c') \/
               p (S n) = None) /\
    (p n = None -> p (S n) = None).

Definition enabled (c : config) (l : label) : Prop :=
  exists c', c ~(l)~> c'.

Definition eventually_processed (l : label) (p : path) : Prop :=
  exists n c c',
    p n = Some c /\ p (S n) = Some c' /\ c ~(l)~> c'.

Definition infinitely_often_enabled (l : label) (p : path) : Prop :=
  forall n c, p n = Some c ->
              enabled c l ->
              exists m c', m > n /\
                           p m = Some c' /\
                           enabled c' l.

Definition is_postfix_of (p' p : path) : Prop :=
  exists n, (forall m, p' m = p (m + n)).

Definition fairness : Prop :=
  forall p p', is_postfix_of p' p ->
               (forall l,
                  infinitely_often_enabled l p' ->
                  eventually_processed l p').
