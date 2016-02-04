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
  Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.seq Ssreflect.eqtype Ssreflect.ssrnat.
  Require Import Actario.fairness Actario.auto Actario.specification Actario.tactics Actario.util.

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
    found 4 p4 p5.
  Qed.

  Theorem receive_3 :
    eventually_receive (factorial_system 3 top) top (nat_msg 6).
  Proof.
    unfold_eventually eventually_receive=> p p0 is_path.
    step_until_stop is_path p0.
    found 22 p22 p23.
  Qed.

  Theorem receive_n' :
    forall n,
      eventually_receive (factorial_system n top) top (nat_msg (fact n)).
  Proof.
    move=> n.
    unfold_eventually eventually_receive=> p p0 is_path.
    step is_path p0=> p1.
    step is_path p1; rewrite eq_refl=> p2.

    generalize dependent n.
    elim.
    - move=> p0 p1 p2.
      step_until_stop is_path p2.
      found 4 p4 p5.
    - move=> n IH p0 p1 p2.
      step is_path p2; rewrite eq_refl=> p3.
      (* p 0 = system n top が帰納法の仮定にあるので証明できない *)
      (* もしかしたら configuration について帰納法？=> 行ける気がする *)
      admit.
  Qed.

  (* initial acc must be 1 *)
  (* gen_cont_n top 3 1 = [:: {|
              state_type := ContState;
              actor_name := generated 2
                              (generated 0 (toplevel "factorial"));
              remaining_actions := become
                                     (val_cust 1
                                        (generated 1
                                           (generated 0
                                              (toplevel "factorial"))));
              next_num := 0;
              behv := factorial_cont_behv;
              queue := [::] |};
              {|
              state_type := ContState;
              actor_name := generated 1
                              (generated 0 (toplevel "factorial"));
              remaining_actions := become
                                     (val_cust 2
                                        (generated 0
                                           (generated 0
                                              (toplevel "factorial"))));
              next_num := 0;
              behv := factorial_cont_behv;
              queue := [::] |};
              {|
              state_type := ContState;
              actor_name := generated 0
                              (generated 0 (toplevel "factorial"));
              remaining_actions := become (val_cust 3 top);
              next_num := 0;
              behv := factorial_cont_behv;
              queue := [::] |}]
   *)
  Fixpoint gen_cont_n (top : name) (n : nat) (acc : nat) :=
    match n with
    | 0 => [::]
    | S n' => match n' with
              | 0 => [:: {|
                          state_type := ContState;
                          actor_name := generated 0 (generated 0 (toplevel "factorial"));
                          remaining_actions := become (val_cust acc top);
                          next_num := 0;
                          behv := factorial_cont_behv;
                          queue := [::] |}]
              | S n'' =>
                {|
                  state_type := ContState;
                  actor_name := generated n' (generated 0 (toplevel "factorial"));
                  remaining_actions := become (val_cust acc (generated n'' (generated 0 (toplevel "factorial"))));
                  next_num := 0;
                  behv := factorial_cont_behv;
                  queue := [::] |} :: gen_cont_n top n' (S acc)
              end
    end.

  Fixpoint gen_done_n (top : name) (n : nat) :=
    match n with
    | 0 => [::]
    | S n' => {|
                  state_type := ContState;
                  actor_name := generated n' (generated 0 (toplevel "factorial"));
                  remaining_actions := become cont_done;
                  next_num := 0;
                  behv := factorial_cont_behv;
                  queue := [::] |} :: gen_done_n top n'
    end.

  Definition path_break_start p (i n : nat)
             cust_st cust_name cust_acts cust_nx cust_behv cust_q
             fact_nx rest :=
    cust_name <> (generated 0 (toplevel "factorial")) /\
    cust_name \notin [seq actor_name i | i <- rest] /\
    p i = Some
            [::
             {|
               state_type := unit;
               actor_name := generated 0 (toplevel "factorial");
               remaining_actions := become tt;
               next_num := fact_nx;
               behv := factorial_behv;
               queue := [:: tuple_msg (nat_msg n) (name_msg cust_name)] |},
             {|
               state_type := cust_st;
               actor_name := cust_name;
               remaining_actions := cust_acts;
               next_num := cust_nx;
               behv := cust_behv;
               queue := cust_q |} & rest].

  Definition path_break_0 p (i n : nat) ini nx cust rest :=
      p i = Some
         [:: {|
             state_type := initializer_state;
             actor_name := toplevel "factorial";
             remaining_actions := become done;
             next_num := 1;
             behv := fun st : initializer_state =>
                     match st with
                     | start =>
                         receive
                           (fun _ : message => initial_actions ini top)
                     | done => receive (fun _ : message => become done)
                     end;
             queue := [::] |},
             {|
             state_type := unit;
             actor_name := generated 0 (toplevel "factorial");
             remaining_actions := become tt;
             next_num := nx;
             behv := factorial_behv;
             queue := [:: tuple_msg (nat_msg n) (name_msg cust)] |} & rest].
  Definition path_break_1 p (i n : nat) ini nx cust rest :=
      p i = Some (
         [:: {|
             state_type := initializer_state;
             actor_name := toplevel "factorial";
             remaining_actions := become done;
             next_num := 1;
             behv := fun st : initializer_state =>
                     match st with
                     | start =>
                         receive
                           (fun _ : message => initial_actions ini top)
                     | done => receive (fun _ : message => become done)
                     end;
             queue := [::] |},
             {|
             state_type := unit;
             actor_name := generated 0 (toplevel "factorial");
             remaining_actions := become tt;
             next_num := nx;
             behv := factorial_behv;
             queue := [:: tuple_msg (nat_msg 0) (name_msg cust)] |} & (gen_cont_n top n 1 ++ rest)]).

  Definition path_break_end p (i n : nat)
             cust_st cust_name cust_acts cust_nx cust_behv
             fact_nx rest :=
    cust_name <> (generated 0 (toplevel "factorial")) /\
    cust_name \notin [seq actor_name i | i <- rest] /\
    p i = Some
            [::
             {|
               state_type := unit;
               actor_name := generated 0 (toplevel "factorial");
               remaining_actions := become tt;
               next_num := fact_nx;
               behv := factorial_behv;
               queue := [::] |},
             {|
               state_type := cust_st;
               actor_name := cust_name;
               remaining_actions := cust_acts;
               next_num := cust_nx;
               behv := cust_behv;
               queue := [:: (nat_msg (fact n))] |} & rest].


  Definition path_break_2 p (i n : nat) ini nx rest :=
      p i = Some (
         [:: {|
             state_type := initializer_state;
             actor_name := toplevel "factorial";
             remaining_actions := become done;
             next_num := 1;
             behv := fun st : initializer_state =>
                     match st with
                     | start =>
                         receive
                           (fun _ : message => initial_actions ini top)
                     | done => receive (fun _ : message => become done)
                     end;
             queue := [:: (nat_msg (fact n))] |},
             {|
             state_type := unit;
             actor_name := generated 0 (toplevel "factorial");
             remaining_actions := become tt;
             next_num := nx;
             behv := factorial_behv;
             queue := [::] |} & (gen_done_n top n ++ rest)]).

  Lemma mult_0 :
    forall n,
      n * 0 = 0.
  Proof.
    elim=>//.
  Qed.

  Lemma add_0 : forall n, n + 0 = n. Proof. elim=>//. Qed.

  Lemma fact_trans_0_1 :
    forall p (i n : nat)
           cust_st cust_name cust_acts cust_nx cust_behv cust_q
           cust_acts'
           fact_nx rest rest',
      is_transition_path p ->
      possible_labels rest = [::] ->
      path_break_start p i n cust_st cust_name cust_acts cust_nx cust_behv cust_q fact_nx rest ->
      path_break_end p (i + 4 * n) n cust_st cust_name cust_acts' cust_nx cust_behv (fact_nx + n) rest'.
  Proof.
















  Qed.

  Lemma fact_trans_1_2 :
    forall p n i rest,
      path_break_1 p i n rest ->
      path_break_2 p (i + 2 * n + 2) n rest. (* fact 3 -> 22 *)
  Proof.
    admit.
  Qed.

  Lemma get_done_n_no_labels :
    forall n,
      possible_labels (gen_done_n top n) = [::].
  Proof.
    elim=>//.
    move=> n /=.
    rewrite/possible_labels/=.
    admit.

  Qed.

  Lemma possible_labels_path_break_2_receive :
    forall n,
      possible_labels ([:: {|
             state_type := initializer_state;
             actor_name := toplevel "factorial";
             remaining_actions := become done;
             next_num := 1;
             behv := fun st : initializer_state =>
                     match st with
                     | start =>
                         receive
                           (fun _ : message => initial_actions n top)
                     | done => receive (fun _ : message => become done)
                     end;
             queue := [:: (nat_msg (fact n))] |};
             {|
             state_type := unit;
             actor_name := generated 0 (toplevel "factorial");
             remaining_actions := become tt;
             next_num := 0;
             behv := factorial_behv;
             queue := [::] |}] ++
         gen_done_n top n) = [:: (Receive (toplevel "factorial") (nat_msg (fact n)))].
  Proof.
    move=> n.
    rewrite/possible_labels/=.
    congr (_ :: _).
    suff H : [seq match a with
          | {| state_type := state_type; actor_name := me;
            remaining_actions := new _ _ _ _; next_num := nx |} =>
              Some (New (generated nx me))
          | {| state_type := state_type; actor_name := me;
            remaining_actions := (to) ! msg; _ |} =>
              if to
                   \in [:: toplevel "factorial",
                           generated 0 (toplevel "factorial")
                         & [seq actor_name i | i <- gen_done_n top n]]
              then Some (Send me to msg)
              else None
          | {| state_type := state_type; actor_name := me;
            remaining_actions := self _ |} => Some (Self me)
          | {| state_type := state_type; actor_name := me;
            remaining_actions := become _; queue := [::] |} => None
          | {| state_type := state_type; actor_name := me;
            remaining_actions := become _; queue :=
            msg :: _ |} => Some (Receive me msg)
          end | a <- gen_done_n top n] = [seq None | a <- gen_done_n top n].
    rewrite H {H}.
    elim: n=>//.
    apply/map_ext_in.
    elim: n=>//.
    move=> n IH a /=.
    case.
    - by move=><-.
    - case: a.
      move=> st nm acts nx tmpl q.
      case: acts.
      + move=> ch_st b c a.
        clear.
        elim: n=>//.
        move=> n IH /=.
        case.
        * case=>//.
        * apply/IH.
      + move=> n0 m a in_a.
        exfalso.
        move: in_a.
        clear.
        elim: n=>//.
        move=> n IH /=.
        case.
        * case=>//.
        * by apply/IH.
      + move=> a in_a; exfalso; move: in_a; clear; elim: n=>//; move=> n IH /=; case; [ by case=>// | by apply/IH ].
      + move=> s; elim: q=>//.
        move=> a l IH' in_a; exfalso; move: in_a; clear; elim: n=>//; move=> n IH /=; case; [ by case=>// | by apply/IH ].
  Qed.

  Lemma finish :
    forall n,
      calc_trans
        ([:: {|
              state_type := initializer_state;
              actor_name := toplevel "factorial";
              remaining_actions := become done;
              next_num := 1;
              behv := fun st : initializer_state =>
                      match st with
                      | start =>
                          receive
                            (fun _ : message => initial_actions n top)
                      | done => receive (fun _ : message => become done)
                      end;
              queue := [:: nat_msg (fact n)] |};
              {|
              state_type := unit;
              actor_name := generated 0 (toplevel "factorial");
              remaining_actions := become tt;
              next_num := 0;
              behv := factorial_behv;
              queue := [::] |}] ++ gen_done_n top n)
        (Receive (toplevel "factorial") (nat_msg (fact n))) =
        ([:: {|
              state_type := initializer_state;
              actor_name := toplevel "factorial";
              remaining_actions := become done;
              next_num := 1;
              behv := fun st : initializer_state =>
                      match st with
                      | start =>
                          receive
                            (fun _ : message => initial_actions n top)
                      | done => receive (fun _ : message => become done)
                      end;
              queue := [::] |};
              {|
              state_type := unit;
              actor_name := generated 0 (toplevel "factorial");
              remaining_actions := become tt;
              next_num := 0;
              behv := factorial_behv;
              queue := [::] |}] ++ gen_done_n top n).
  Proof.
    move=> n /=.
    rewrite eq_refl.
    congr (_ :: _ :: _).
    elim: n=>//.
    move=> n IH /=.
    congr (_ :: _).
    have H : [seq match a with
            | {| state_type := st; actor_name := nm; remaining_actions :=
              new _ _ _ _ |} => a
            | {| state_type := st; actor_name := nm; remaining_actions :=
              (_) ! _; _ |} => a
            | {| state_type := st; actor_name := nm; remaining_actions :=
              self _ |} => a
            | {| state_type := st; actor_name := nm; remaining_actions :=
              become s; next_num := nx; behv := b; queue := [::] |} => a
            | {| state_type := st; actor_name := nm; remaining_actions :=
              become s; next_num := nx; behv := b; queue :=
              hd :: tl |} =>
                if (nm == toplevel "factorial") &&
                   (hd == nat_msg (fact n))
                then
                 {|
                 state_type := st;
                 actor_name := nm;
                 remaining_actions := interp (b s) hd;
                 next_num := nx;
                 behv := b;
                 queue := tl |}
                else a
                  end | a <- gen_done_n top n] =
               [seq match a with
        | {| state_type := st; actor_name := nm; remaining_actions := new
          _ _ _ _ |} => a
        | {| state_type := st; actor_name := nm; remaining_actions :=
          (_) ! _; _ |} => a
        | {| state_type := st; actor_name := nm; remaining_actions := self
          _ |} => a
        | {| state_type := st; actor_name := nm; remaining_actions :=
          become s; next_num := nx; behv := b; queue := [::] |} => a
        | {| state_type := st; actor_name := nm; remaining_actions :=
          become s; next_num := nx; behv := b; queue :=
          hd :: tl |} =>
            if (nm == toplevel "factorial") &&
               (hd == nat_msg (n.+1 * fact n))
            then
             {|
             state_type := st;
             actor_name := nm;
             remaining_actions := interp (b s) hd;
             next_num := nx;
             behv := b;
             queue := tl |}
            else a
        end | a <- gen_done_n top n].
    apply/map_ext_in.
    case=> st nm acts nx tmpl q {IH}; case: acts=>//.
    elim: q=>//.
    move=> a l IH s contra; exfalso.
    move: contra; clear.
    elim: n=>//.
    move=> n IH /= contra.
    apply IH; case: contra; done.

    rewrite -H.
    done.
  Qed.

  Theorem receive_n :
    forall n,
      eventually_receive (factorial_system n top) top (nat_msg (fact n)).
  Proof.
    move=> n.
    unfold_eventually eventually_receive=> p p0 is_path.
    step is_path p0=> p1.
    step is_path p1; rewrite eq_refl=> p2.
    move: fact_trans_0_1.
    move/(_ p n 2 _ p2)=> pb1.
    move: fact_trans_1_2.
    move/(_ p n _ _ pb1).
    rewrite/path_break_2=> pfin.
    eexists; eexists; eexists.
    split; last split.
    - apply pfin.
    - move/(_ _ _ _ is_path pfin): trace_path.
      rewrite cats0 possible_labels_path_break_2_receive.
      rewrite/any1.
      apply.
    - rewrite finish.
      eapply trans_receive.
      + apply/Permutation_refl.
      + rewrite cats0; apply/Permutation_refl.
  Qed.
End Verification.
