Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Sorting.Permutation.
Require Import Actario.syntax Actario.semantics Actario.fairness Actario.properties.

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
  Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.seq Ssreflect.ssrnat.

  Definition initial_actions (n : nat) (parent : name) := (
    x <- new factorial_behv with tt;
    x ! tuple_msg (nat_msg n) (name_msg parent);
    become tt).

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
    rewrite/eventually_receive/eventually_do_label/is_transition_path=> p p_ini p_is_path.
    rewrite/eventually_processed.
    pose (c0 := (factorial_system 0 top)).
    set p_is_path as p1; move/(_ 0): p1.
    case; move/(_ c0 p_ini).
    case.
    case=> c1.
    case=> l1.
    case=> p1.
    rewrite/c0.
    case: l1.
    move=> to msg falso; inversion falso.





    Focus 2.








      Theorem receive_1 :
        receive_exists (factorial_system 0 top) top (nat_msg 1).
      Proof.
        pose (factorial := (generated 0 top)).
        rewrite/receive_exists.
        eexists; eexists.
        split.
        - rewrite/factorial_system/init/initial_actions => //.
          eapply trans_trans.
          {
            exists (New factorial).
            apply/trans_new.
            Focus 10.
            apply/Permutation_refl.
            Focus 2.
            apply/Permutation_refl.
          }
          eapply trans_trans.
          {
            exists (Send top factorial (tuple_msg (nat_msg 0) (name_msg top))).
            apply/trans_send.
            Focus 13.
            apply/perm_swap.
            Focus 2.
            apply/perm_swap.
          }
          eapply trans_trans.
          {
            exists (Receive factorial top (tuple_msg (nat_msg 0) (name_msg top))).
            apply/trans_receive.
            Focus 8.
            apply/Permutation_refl.
            Focus 2.
            apply/Permutation_refl.
          }
          eapply trans_trans.
          {
            exists (Send factorial top (nat_msg 1)).
            apply/trans_send.
            Focus 13.
            apply/Permutation_refl.
            Focus 2.
            apply/Permutation_refl.
          }
          eapply trans_refl.
          apply/perm_swap.
        - eexists.
          apply/trans_receive.
          Focus 9.
          apply/Permutation_refl.
          Focus 3.
          apply/Permutation_refl.
          apply factorial.
      Qed.

      Theorem receive_n :
        forall n,
          receive_exists (factorial_system n top) top (nat_msg (fact n)).
      Proof.
        pose (factorial := generated 0 top).
        move=> n.
        rewrite/receive_exists.
        eexists.
        exists (generated 0 factorial).
        split.
        case: n.




        elim: n.
        - exact: receive_1.
        - rewrite/receive_exists; move=> n.
          case; move=> actors; case=> from; case=> fact_n; case=> actors' IH.
          eexists.
          exists from.
          split.
          + rewrite/factorial_system/init/initial_actions.
            eapply trans_trans.
            {
              exists (New factorial).
              apply/trans_new.
              Focus 10.
              apply/Permutation_refl.
              Focus 2.
              apply/Permutation_refl.
            }
            eapply trans_trans.
            {
              exists (Send top factorial (tuple_msg (nat_msg n.+1) (name_msg top))).
              apply/trans_send.
              Focus 13.
              apply/perm_swap.
              Focus 2.
              apply/perm_swap.
            }
            eapply trans_trans.
            {
              exists (Receive factorial top (tuple_msg (nat_msg n.+1) (name_msg top))).
              apply/trans_receive.
              Focus 8.
              apply/Permutation_refl.
              Focus 2.
              apply/Permutation_refl.
            }
            eapply trans_trans.
            {
              exists (New (generated 0 factorial)).
              apply/trans_new.
              Focus 10.
              apply/Permutation_refl.
              Focus 2.
              apply/Permutation_refl.
            }


            case; move=> [ sendings actors ]; case=> from; case=> fact_n; case=> c' IH.
            exists ([:: Build_sending (toplevel "factorial") (generated 0 (generated 0 (toplevel "factorial"))) (nat_msg (fact n+1))] ><
                                                                                                                                      (take n actors ++
                                                                                                                                            [:: Build_actor (generated 0 (generated 0 (toplevel "factorial"))) (become empty_behv) 0
                                                                                                                                             ; Build_actor (generated 0 (toplevel "factorial")) (become empty_behv) n.+2
                                                                                                                                             ; Build_actor (toplevel "factorial") (become empty_behv) 1])).
            exists (generated 0 (generated 0 (toplevel "factorial"))).
            split.
          + rewrite/factorial_system/init.
            apply: trans_trans.
      Admitted.
End Verification.
