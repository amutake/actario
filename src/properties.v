Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.seq.

Require Import syntax semantics fairness.

Definition receive_exists (ini : config) (to : name) (content : message) :=
  exists c,
    ini ~>* c /\ (exists c', c ~(Receive to content)~> c').

Definition eventually_do_label (ini : config) (l : label) :=
  forall p : path,
    p 0 = Some ini ->
    is_transition_path p ->
    eventually_processed l p.

Definition eventually_receive (ini : config) (to : name) (msg : message) :=
  eventually_do_label ini (Receive to msg).
Definition eventually_send (ini : config) (from : name) (to : name) (msg : message) :=
  eventually_do_label ini (Send from to msg).

(* Definition receive_exists_with_behv (ini : config) (to : name) (content : message) (behv : behavior) := *)
(*   exists from sendings actors_l actors_r next, *)
(*     let c := (actors_l ++ Build_actor to (become behv) next :: actors_r) in *)
(*     ini ~>* c /\ (exists c', c ~(Receive to from content)~> c'). *)

(* (msg : message) じゃなくて (P : msg -> Prop) とかのほうが良さそう *)

(* eventually: どんな遷移列を経ても、必ずいつかはある性質が満たされる *)

(* こんなイメージ
 * o : 起点, x : ある性質が満たされる点
 *
 *           +---x-..
 *     +-----+                +--x-..
 *     |     |    +---x-..    |
 *     |     +----+------x-.. +------x-..
 * o --+                      |
 *     |    +--x-.. +---------+
 *     |    |       |         |
 *     +----+-------+---x-..  +---x-..
 *
 *
 *)
