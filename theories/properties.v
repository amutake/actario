Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Import ListNotations.

Require Import syntax semantics.

Definition deliver_exists (ini : config) (target : name) (msg : message) :=
  exists global_queue actions queue number actors_l actors_r,
    let c := (conf (send_message target msg :: global_queue)
              (actors_l
                 ++ actor_state target actions queue number
                 :: actors_r)) in
    ini ~>* c /\ (exists c', c ~(Deliver)~> c').

Definition open_exists (ini : config) (target : name) (msg : message) :=
  exists global_queue behv queue number actors_l actors_r,
    forall c,
    c = (conf global_queue
              (actors_l
                 ++ actor_state target (become behv) (msg :: queue) number
                 :: actors_r)) ->
    ini ~>* c /\ (exists c', c ~(Open)~> c').

Definition open_exists_with_behv (ini : config) (target : name) (msg : message) (behv : behavior) :=
  exists global_queue queue number actors_l actors_r,
    forall c,
    c = (conf global_queue
              (actors_l
                 ++ actor_state target (become behv) (msg :: queue) number
                 :: actors_r)) ->
    ini ~>* c /\ (exists c', c ~(Open)~> c').

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
