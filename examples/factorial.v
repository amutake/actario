Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.seq Ssreflect.ssrnat.
Require Import Actario.syntax Actario.semantics Actario.properties.

(**
 * ref: An Algebraic Theory of Actors and its Actors and Application to a Simple Object-Based Language (Gul Agha, 2004)
 * page: 7
 *)

CoFixpoint factorial_cont_behv (val : nat) (cust : name) : behavior :=
  receive (fun msg =>
         match msg with
           | nat_msg arg =>
             cust ! nat_msg (val * arg);
             become empty_behv
           | _ => become (factorial_cont_behv val cust)
         end).

CoFixpoint factorial_behv : behavior :=
  receive (fun msg =>
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

Definition factorial_system (n : nat) (parent : name) : config :=
  init "factorial" (
         x <- new factorial_behv;
         x ! tuple_msg (nat_msg n) (name_msg parent);
         become empty_behv
       ).

Recursive ActorExtraction factorial_system.
ActorExtraction "factorial" factorial_system.

Open Scope string_scope.

Fixpoint fact (n : nat) :=
  match n with
    | O => 1
    | S n => S n * (fact n)
  end.

Section FactorialCorrect.
  (* (factorial_system 0) から、(toplevel "factorial") に向けて (nat_msg 1) というメッセージが送られる遷移とそこまでの遷移列が存在する *)
  (* toplevel 使って名前を指定するところが微妙 *)
  (* forall parent,
   *   deliver_exists (factorial_system 0 parent) parent (nat_msg 1).
   * としたいが、external actor へのメッセージ送信には対応できていない
   *)
  Theorem receive_1 :
    receive_exists (factorial_system 0 (toplevel "factorial")) (toplevel "factorial") (nat_msg 1).
  Proof.
    pose (top := toplevel "factorial").
    pose (factorial := (generated 0 top)).

    rewrite/receive_exists.
    admit.
    (* exists [], (become empty_behv), [], 1. *)
    (* exists [actor_state factorial (become factorial_behv) 0], []. (* gen_number, actors_l, actors_r とか何でも良くない？ *) *)
    (* simpl; split. *)
    (* - unfold factorial_system. *)
    (*   pose (fact_actor := actor_state factorial (become factorial_behv) [] 0). *)
    (*   pose (top_actor := actor_state top (become empty_behv) [] 1). *)
    (*   pose (msg0 := tuple_msg (nat_msg 0) (name_msg top)). *)
    (*   pose (conf1 := conf [] *)
    (*                       [ fact_actor; *)
    (*                         actor_state top (factorial ! msg0; *)
    (*                                          become empty_behv) [] 1 *)
    (*                       ]). *)
    (*   eapply trans_trans. *)
    (*   (* 遷移を1つずつ証明しないといけなくて、かなり小規模なものでも粒度細かすぎてめんどくさい。。 *) *)
    (*   { *)
    (*     exists New. *)
    (*     assert (init "factorial" ( *)
    (*                    (x) <- new factorial_behv; *)
    (*                    (x) ! msg0 ; become empty_behv *)
    (*                  ) ~(New)~> conf1). *)
    (*     { *)
    (*       unfold init. *)
    (*       apply trans_new with (actors_l := []). *)
    (*     } *)
    (*     apply H. *)
    (*   } *)
    (*   pose (conf2 := conf [send_message factorial msg0] *)
    (*                       [ fact_actor; top_actor ]). *)
    (*   eapply trans_trans. *)
    (*   { *)
    (*     exists Send. *)
    (*     assert (conf1 ~(Send)~> conf2). *)
    (*     { *)
    (*       apply trans_send with (actors_l := [fact_actor]). *)
    (*     } *)
    (*     apply H. *)
    (*   } *)
    (*   pose (conf3 := conf [] *)
    (*                       [ actor_state factorial (become factorial_behv) [msg0] 0; *)
    (*                         top_actor]). *)
    (*   eapply trans_trans. *)
    (*   { *)
    (*     exists Deliver. *)
    (*     assert (conf2 ~(Deliver)~> conf3). *)
    (*     { *)
    (*       apply trans_deliver with (actors_l := []). *)
    (*     } *)
    (*     apply H. *)
    (*   } *)
    (*   pose (conf4 := conf [] *)
    (*                       [ actor_state factorial (top ! nat_msg 1; become factorial_behv) [] 0; *)
    (*                         top_actor]). *)
    (*   eapply trans_trans. *)
    (*   { *)
    (*     exists Open. *)
    (*     assert (conf3 ~(Open)~> conf4). *)
    (*     { *)
    (*       apply trans_open with (actors_l := []). *)
    (*     } *)
    (*     apply H. *)
    (*   } *)
    (*   pose (conf5 := conf [send_message top (nat_msg 1)] [fact_actor; top_actor]). *)
    (*   eapply trans_trans. *)
    (*   { *)
    (*     exists Send. *)
    (*     assert (conf4 ~(Send)~> conf5). *)
    (*     { *)
    (*       apply trans_send with (actors_l := []). *)
    (*     } *)
    (*     apply H. *)
    (*   } *)
    (*   apply trans_refl. *)
    (* - exists (conf [] *)
    (*                [ actor_state factorial (become factorial_behv) [] 0; *)
    (*                  actor_state top (become empty_behv) [nat_msg 1] 1]). *)
    (*   apply trans_deliver with (actors_l := [actor_state factorial (become factorial_behv) [] 0]). *)
  Qed.

  Theorem receive_n :
    forall n,
      receive_exists (factorial_system n (toplevel "factorial")) (toplevel "factorial") (nat_msg (fact n)).
  Proof.
    move=> n.
    elim: n.
    - exact: receive_1.
    - rewrite/receive_exists; move=> n.
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
End FactorialCorrect.
