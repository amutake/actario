Set Implicit Arguments.
Unset Strict Implicit.

Require Import NPeano Actor.syntax Actor.semantics.

(**
 * ref: An Algebraic Theory of Actors and its Actors and Application to a Simple Object-Based Language (Gul Agha, 2004)
 * page: 7
 *)

CoFixpoint factorial_cont_behv (val : nat) (cust : name) : behavior :=
  beh (fun msg =>
         match msg with
           | nat_msg arg =>
             cust ! nat_msg (val * arg);
             become empty_behv
           | _ => become (factorial_cont_behv val cust)
         end).

CoFixpoint factorial_behv : behavior :=
  beh (fun msg =>
         match msg with
           | tuple_msg (nat_msg 0) (name_msg cust) =>
             cust ! nat_msg 1;
             become factorial_behv
           | tuple_msg (nat_msg (S n)) (name_msg cust) =>
             cont <- new (factorial_cont_behv (S n) cust);
             me <- self;
             me ! tuple_msg (nat_msg n) (name_msg cont);
             become factorial_behv
           | _ => become factorial_behv
         end).

Definition result_wait_behv (expect : nat) : behavior :=
  beh (fun msg =>
         match msg with
           | nat_msg result =>
             (* n を観測したい *)
             if (Nat.eqb result expect) then
               (* OK *)
               become empty_behv
             else
               (* まちがってる *)
               become empty_behv
           | _ => become empty_behv
         end).

Definition factorial_system : config :=
  init "factorial" (
         x <- new factorial_behv;
         me <- self;
         x ! tuple_msg (nat_msg 5) (name_msg me);
         become (result_wait_behv (5 * 4 * 3 * 2 * 1))
       ).

(* OK 状態にくることを検証したいのだけど、どうやればいいのか *)
