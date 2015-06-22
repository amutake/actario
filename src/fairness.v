Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.eqtype Ssreflect.ssrbool Ssreflect.seq.
Require Import syntax semantics.

(* applpi 形式の Transition Path (: nat -> option config) を導入するなら、下の定理が必要。
 * なぜかというと、TP n と TP (S n) の間について、別なラベルで遷移できてしまうなら、
 * label 情報を持っておらず前後の config 情報でラベルを判断する TP では、
 * そのラベルで遷移したことを表す述語、例えば eventually processed が意味をなさなくなってしまうから。
 *)
(* この証明が本当にラベルの一意性を表しているのかは検討の余地がある。trans の定義で、seq と集合のギャップがあるところが怪しい *)
Theorem label_unique : forall c c' l1 l2,
                         c ~(l1)~> c' ->
                         c ~(l2)~> c' ->
                         l1 == l2.
Proof.
  move=> c c' l1 l2 t1.
  move: l2.
  elim: t1; [do 7 move=> ?|do 7 move=> ?|do 6 move=> ?|do 5 move=> ?];
  case=> [? ? ?|? ? ?|? ?|?] tr2; by inversion tr2.
Qed.

Reserved Notation "c1 '~>(' n ')' c2" (at level 70).

Inductive indexed_trans_star : nat -> config -> config -> Prop :=
| trans_zero : forall c, c ~>(0) c
| trans_succ : forall c1 c2 c3 n, (exists l, c1 ~(l)~> c2) ->
                                  c2 ~>(n) c3 ->
                                  c1 ~>(S n) c3
where "c1 '~>(' n ')' c2" := (indexed_trans_star n c1 c2).

Hint Constructors indexed_trans_star.


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

(* Definition will_be_enabled (c : config) (l : label) : Prop := *)
(*   exists c', c ~>* c' /\ enabled c' l. *)

(* Definition stable (c : config) : Prop := *)
(*   forall l, ~ enabled c l. *)

(* Definition infinitely_often_enabled {c c' : config} (path : c ~>* c') (l : label) := *)
(*   exists c'', c' ~>* c'' -> enabled c'' l. *)

(* CoInductive indexed_trans_path (c : config) : nat -> Set := *)
(* | trans_end : forall n, indexed_trans_path c n -> *)
(*                         stable c' -> *)
(*                         indexed_trans_path c n *)

(* (* We deal with only infinite sequence *)
(*  * because finite sequence always satisfies fairness property *)
(*  *) *)

(* Fixpoint ev_reduced (c c' : config) (path : c ~>* c') *)

(* Definition IOE : *)
(*   forall c1 c2 c3 l, *)
(*     c1 ~>* c2 -> *)
(*     enabled c2 l -> *)
(*     c2 ~>* c3 -> *)


(* Definition fairness := *)
(*   forall c1 c2 c3 l, *)
(*     c1 ~>* c2 -> *)
(*     enabled c2 l -> *)
(*     ~ will_be_enabled c2 l \/ *)
