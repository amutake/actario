Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.seq.

Require Import syntax semantics.

Definition receive_exists (ini : config) (to : name) (content : message) :=
  exists c from,
    ini ~>* c /\ (exists c', c ~(Receive to from content)~> c').

Definition receive_exists_with_behv (ini : config) (to : name) (content : message) (behv : behavior) :=
  exists from sendings actors_l actors_r next,
    let c := sendings >< (actors_l ++ Build_actor to (become behv) next :: actors_r) in
    ini ~>* c /\ (exists c', c ~(Receive to from content)~> c').

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
