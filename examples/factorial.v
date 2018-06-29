Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Sorting.Permutation.
Require Import Actario.syntax Actario.semantics.

(**
 * ref: An Algebraic Theory of Actors and its Actors and Application to a Simple Object-Based Language (Gul Agha, 2004)
 * page: 7
 *)

Inductive ContState : Set :=
| val_cust : nat -> name -> ContState
| cont_done : ContState.

Definition factorial_cont_behv (state : ContState) : behavior ContState :=
  receive (fun msg =>
             match msg, state with
             | nat_msg arg, val_cust val cust =>
               cust ! nat_msg (val * arg);
               become cont_done
             | _, _ => become state
             end).

Definition factorial_behv (state : unit) : behavior unit :=
  receive (fun msg =>
         match msg with
           | tuple_msg (nat_msg 0) (name_msg cust) =>
             cust ! nat_msg 1;
             become tt
           | tuple_msg (nat_msg (S n)) (name_msg cust) =>
             cont <- new factorial_cont_behv with (val_cust (S n) cust);
             me <- self;
             me ! tuple_msg (nat_msg n) (name_msg cont);
             become tt
           | _ => become tt
         end).

Recursive ActorExtraction factorial_behv.
ActorExtraction "factorial" factorial_behv.

(* Verification *)

Section Verification.
  Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.seq mathcomp.ssreflect.ssrnat.
  Require Import Actario.auto Actario.specification Actario.tactics.

  Definition initial_actions (n : nat) (parent : name) := (
    x <- new factorial_behv with tt;
    x ! tuple_msg (nat_msg n) (name_msg parent);
    become done).

  Definition factorial_system (n : nat) (parent : name) : config :=
    init "factorial" (initial_actions n parent).

  Open Scope string_scope.

  Fixpoint fact (n : nat) :=
    match n with
    | O => 1
    | S n => S n * (fact n)
    end.

  (* (factorial_system 0) から、(toplevel "factorial") に向けて (nat_msg 1) というメッセージが送られる遷移とそこまでの遷移列が存在する *)
  (* toplevel 使って名前を指定するところが微妙 *)
  (* forall parent,
   *   deliver_exists (factorial_system 0 parent) parent (nat_msg 1).
   * としたいが、external actor へのメッセージ送信には対応できていない
   *)
  Definition system_name := "factorial".
  Definition top := toplevel system_name.

  Theorem receive_0 :
    eventually_receive (factorial_system 0 top) top (nat_msg 1).
  Proof.
    unfold_eventually eventually_receive=> p p0 is_path.
    step_until_stop is_path p0.
    finish 4 p4 p5.
  Qed.

  Theorem receive_3 :
    eventually_receive (factorial_system 3 top) top (nat_msg 6).
  Proof.
    unfold_eventually eventually_receive=> p p0 is_path.
    step_until_stop is_path p0.
    finish 22 p22 p23.
  Qed.
End Verification.
