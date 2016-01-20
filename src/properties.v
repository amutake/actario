Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrnat.
Require Import Coq.Sorting.Permutation.
Require Import syntax semantics fairness.

(* for proof automation *)

Fixpoint cat_options {A : Type} (opts : seq (option A)) :=
  match opts with
  | [::] => [::]
  | None :: opts' => cat_options opts'
  | Some a :: opts' => a :: cat_options opts'
  end.

Definition possible_labels (c : config) : seq label :=
  cat_options (map (fun a =>
    match a with
    | {| actor_name := to; remaining_actions := become _; queue := msg :: msgs |} =>
      Some (Receive to msg)
    | {| actor_name := fr; remaining_actions := send to msg _ |} =>
      if to \in (map actor_name c) then Some (Send fr to msg) else None (* actually, false case will not happen (because of no external actor) *)
    | {| actor_name := p; remaining_actions := new _ temp ini _; next_num := nx |} =>
      Some (New (generated nx p))
    | {| actor_name := me; remaining_actions := self _ |} =>
      Some (Self me)
    | _ => None
   end) c).

Lemma possible_labels_possible :
  forall c l,
    l \in possible_labels c ->
    exists c',
      c ~(l)~> c'.
Proof.
  elim=>//.
  case=> st nm acts nx bt q.
  move=> c IH l.
  case: acts.
  (* New *)
  - move=> child_st child_bt child_ini cont.
    rewrite/possible_labels/= in_cons.
    case/orP.
    + move/eqP=> ?; subst.
      eexists.
      eapply trans_new; by apply/Permutation_refl.
    + admit.
  - admit.
  - admit.
  - admit.
Qed.

Lemma not_possible_labels_not_possible :
  forall c l,
    l \notin possible_labels c ->
    forall c',
      ~ (c ~(l)~> c').
Proof.
  admit.
Qed.

(* 遷移前とラベルから遷移後のものを一つ返す *)
(* 決定可能になるはず *)
Definition calc_trans (c : config) (l : label) : config :=
  match l with
  | Receive to msg =>
    map (fun a => match a with
                  | {| state_type := st;
                       actor_name := nm;
                       remaining_actions := become s;
                       next_num := nx;
                       behv := b;
                       queue := hd :: tl
                    |} => if (nm == to) && (hd == msg) then (* ok because of no dup *)
                            {| state_type := st;
                               actor_name := nm;
                               remaining_actions := interp (b s) hd;
                               next_num := nx;
                               behv := b;
                               queue := tl
                            |}
                          else
                            a
                  | _ => a
                  end
        ) c
  | Send fr to msg =>
    map (fun a => match a with
                  | {| state_type := st;
                       actor_name := nm;
                       remaining_actions := send t m cont;
                       next_num := nx;
                       behv := b;
                       queue := q
                    |} => if (nm == fr) && (m == msg) then (* ok because of no dup *)
                            {| state_type := st;
                               actor_name := nm;
                               remaining_actions := cont;
                               next_num := nx;
                               behv := b;
                               queue := if (nm == to) then q ++ [:: msg] else q
                            |}
                          else a
                  | {| state_type := st;
                       actor_name := nm;
                       remaining_actions := acts;
                       next_num := nx;
                       behv := b;
                       queue := q
                    |} => if (nm == to) then (* ok because of no dup *)
                            {| state_type := st;
                               actor_name := nm;
                               remaining_actions := acts;
                               next_num := nx;
                               behv := b;
                               queue := q ++ [:: msg]
                            |}
                          else a
                  end
        ) c
  | New (generated g p) =>
    flatten (map (fun a => match a with
                           | {| state_type := st;
                                actor_name := nm;
                                remaining_actions := new child_st tmpl ini cont;
                                next_num := nx;
                                behv := b;
                                queue := q
                             |} => if (nm == p) && (nx == g) then (* ok because of no dup *)
                                     [:: {| state_type := st;
                                            actor_name := nm;
                                            remaining_actions := cont (generated nx nm);
                                            next_num := S nx;
                                            behv := b;
                                            queue := q
                                         |};
                                       {| state_type := child_st;
                                          actor_name := generated nx nm;
                                          remaining_actions := become ini;
                                          next_num := 0;
                                          behv := tmpl;
                                          queue := [::]
                                       |}]
                                   else [:: a]
                           | _ => [:: a]
                           end) c)
  | Self me =>
    map (fun a => match a with
                  | {| state_type := st;
                       actor_name := nm;
                       remaining_actions := self cont;
                       next_num := nx;
                       behv := b;
                       queue := q
                    |} => if (nm == me) then (* ok because of no dup *)
                            {| state_type := st;
                               actor_name := nm;
                               remaining_actions := cont nm;
                               next_num := nx;
                               behv := b;
                               queue := q
                            |}
                          else a
                  | _ => a
                  end) c
  | _ => c
  end.

Theorem calc_trans_sound :
  forall c c' l,
    c' = calc_trans c l ->
    c <> c' ->                  (* if after calc_trans is not changed, then it could not transition *)
    c ~(l)~> c'.
Proof.
  admit.
Qed.

Theorem possible_labels_can_calc_trans :
  forall c l,
    l \in possible_labels c ->
    c ~(l)~> calc_trans c l.
Proof.
  admit.
Qed.

Require Coq.Lists.List.

Fixpoint any1 {A : Type} (p : A -> Prop) (d : Prop) (s : seq A) :=
  match s with
  | [::] => d
  | [:: h] => p h
  | h :: t => p h \/ any1 p d t
  end.

Theorem trace_path :
  forall p i c,
    is_transition_path p ->
    p i = Some c ->
    any1 (fun l => p (S i) = Some (calc_trans c l)) (* exhaustive by path_perm *)
         (p (S i) = None)                      (* if possible_labels is empty *)
         (possible_labels c).
Proof.
  admit.
Qed.

(* for describing spec *)

Definition receive_exists (ini : config) (to : name) (content : message) :=
  exists c,
    ini ~>* c /\ (exists c', c ~(Receive to content)~> c').

Definition eventually_do_label (c0 : config) (l : label) :=
  forall p : path,
    p 0 = Some c0 ->
    is_transition_path p ->
    eventually_processed l p.

Definition eventually_receive (c0 : config) (to : name) (msg : message) :=
  eventually_do_label c0 (Receive to msg).
Definition eventually_send (c0 : config) (from : name) (to : name) (msg : message) :=
  eventually_do_label c0 (Send from to msg).

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
