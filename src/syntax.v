Declare ML Module "actor_extraction_plugin".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Strings.String.
Require Import Ssreflect.ssreflect Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import ssrstring.

Notation machine_addr := string.
Notation gen_number := nat.

Section Name.
  Inductive name : Set :=
  | toplevel : machine_addr -> name
  | generated : gen_number -> name -> name. (* ユーザーに generated というコンストラクタを使わせたくないのだけどできる？ *)

  Fixpoint eqname (n1 n2 : name) : bool :=
    match n1, n2 with
      | toplevel m1, toplevel m2 => m1 == m2
      | generated g1 n1, generated g2 n2 => (g1 == g2) && eqname n1 n2
      | _, _ => false
    end.

  Lemma eqnameP : Equality.axiom eqname.
  Proof.
    elim=> [m1|g1 n1 IHn] [m2|g2 n2].
    - rewrite/=.
      by apply: (iffP eqP) => [->|[]].
    - by right.
    - by right.
    - simpl.
      apply: (iffP andP).
      + case => eqg eqn.
        congr (generated _ _).
        * by move/eqP: eqg.
        * move: IHn; move/(_ n2) => IHn.
            by move/IHn: eqn =><-.
      + case=> <- <-.
        split.
        * apply: eq_refl.
        * by apply (rwP (IHn n1)).
  Qed.

  Canonical name_eqMixin := EqMixin eqnameP.
  Canonical name_eqType := Eval hnf in EqType name name_eqMixin.
End Name.

Section Message.
  (* 任意の Set をメッセージとして送ることができるようにするなら、message と name と actor と behavior に型タグ付けないといけない (と思う)
   * Inductive message (A : Set) : Set := wrap : A -> message A. みたいに。じゃないとパターンマッチできない
   *
   * Inductive message : Type := wrap : forall A : Set, A -> message.
   * match msg with
   *   | wrap nat n => addr ! wrap (n + 1); become empty_behv
   *   | _ => become empty_behv
   * end
   *
   * とかできるかな？と思ったけどできなかった (n has type 'nat' but it is expected to have type 'Datatype.nat' とか言われる。同じなんだけど => nat という変数名にバインドされてるからか。でも型でパターンマッチすることはできない (要出典) から、やっぱできない)
   * あとタプルを作るやつが Set じゃなくて Type だったのでメッセージにできなかった
   *
   * ターゲットを Erlang にするなら、Erlang のプリミティブをサポートするだけでいいかもしれない。
   * atom は string をラップするだけでいい。Extraction のときに string を atom に変換する。
   * Inductive atom : Set := mk_atom : string -> atom.
   *)

  Inductive message : Set :=
  | empty_msg : message
  | name_msg : name -> message
  | str_msg : string -> message
  | nat_msg : nat -> message
  | bool_msg : bool -> message
  | tuple_msg : message -> message -> message.

  Fixpoint eqmessage (m1 m2 : message) : bool :=
    match m1, m2 with
      | empty_msg, empty_msg => true
      | name_msg n1, name_msg n2 => n1 == n2
      | str_msg s1, str_msg s2 => s1 == s2
      | nat_msg n1, nat_msg n2 => n1 == n2
      | bool_msg b1, bool_msg b2 => b1 == b2
      | tuple_msg t11 t12, tuple_msg t21 t22 =>
        eqmessage t11 t21 && eqmessage t12 t22
      | _, _ => false
    end.

  Lemma eqmessageP : Equality.axiom eqmessage.
  Proof.
    elim=> [|n1|s1|n1|b1|t11 IHt1 t12 IHt2] [|n2|s2|n2|b2|t21 t22];
      do [ by apply: (iffP eqP) => [<-|[]] | by constructor | ].
    rewrite/=.
    apply: (iffP andP).
    - case=> eqt1 eqt2.
      congr (tuple_msg _ _).
      + by move/IHt1: eqt1.
      + by move/IHt2: eqt2.
    - case=> <- <-.
      split.
      + by apply (rwP (IHt1 t11)).
      + by apply (rwP (IHt2 t12)).
  Qed.

  Canonical message_eqMixin := EqMixin eqmessageP.
  Canonical message_eqType := Eval hnf in EqType message message_eqMixin.
End Message.

Section Action.
  (* behavior は become で自分を指定することがよくあり、Inductive だとそのような再帰が書けなくなるので、CoInductive にしている *)
  (* CoInductive なので、無限ループが書けちゃう *)
  (* Inductive actions, CoInductive behavior な気がするけど、相互(余)帰納型でそういうのって書ける(正しい)の？ *)
  (* CoInductive なので eqType にできない (CoFixpoint f : actions -> actions -> bool となるような関数を書けない) *)
  (* CoFixpoint actions_example : actions :=
   *   let behv := beh (fun _ => actions_example) in
   *   become behv
   * とかするから、actions も CoInductive で良さそう
   *)
  (* use nat as state *)
  Inductive actions (state : Set) : Type :=
  | new : forall child_state : Set, (child_state -> behavior child_state) -> child_state -> (name -> actions state) -> actions state (* CPS, initial state is 0 *)
  | send : name -> message -> actions state -> actions state   (* send n m a == n ! m; a *)
  | self : (name -> actions state) -> actions state           (* CPS *)
  | become : state -> actions state                   (* become した後はアクションを取れない。become 以外は後に actions が続かなければならないので、次のメッセージを受け取れる状態になれば必ず become になる *)
  with behavior (state : Set) : Type :=
  | receive : (message -> actions state) -> behavior state.

  Definition behavior_template (state : Set) := state -> behavior state.
  Definition interp {state : Set} (b : behavior state) (m : message) : actions state :=
    match b with
    | receive f => f m
    end.
  (* eqactions, eqbehavior は定義できない。(2つの関数を受け取って bool を返すような関数を作らなければいけないから (同じ形をしているかどうかさえ判定してくれればそれでいいけど…)) *)

  (* Lemma "アクションに終わりがあるなら、アクションの最後は become しか来ない"
   * CoInductive なので action := send name msg action みたいなのが書けるから自明ではないんだけど、これ証明できるの？
   * become = "ある振る舞いでもって、次のメッセージの待ち状態になる" という意味だからいいのか
   * => CoInductive ではなくなった
   *)
End Action.

Notation "n '<-' 'new' behv 'with' ini ; cont" := (new behv ini (fun n => cont)) (at level 0, cont at level 10).
Notation "n '!' m ';' a" := (send n m a) (at level 0, a at level 10).
Notation "me '<-' 'self' ';' cont" := (self (fun me => cont)) (at level 0, cont at level 10).

(* Build_actor (このアクターの名前) (まだ実行していないアクション) (生成番号) *)
Record actor := {
                 state_type : Set;
                 actor_name : name;
                 remaining_actions : actions state_type;
                 next_num : gen_number;
                 behv : behavior_template state_type;
                 queue : seq message
               }.
(* behavior は持ってない。actions の最後に次の behavior が来るのと、アクションをし終わった (つまり become がでてきた) 状態のアクターしかメッセージを受け取れないので。でもこれはアクターとしてどうなの？外からは見えないものだけど。。 *)
(* あと、グローバルメッセージキューの他に actor もメッセージキューを持つようにしたい。グローバルキューだけだと、先頭のメッセージの宛先のアクターがいつまでたっても仕事が終わらないとき、他のアクターはメッセージを受け取れない -> configuration の中のメッセージの順番をなくせばOK *)

Definition config := seq actor.

(* メッセージを受け取っても何もしない振る舞い *)
Definition empty_behv {state : Set} (st : state) : behavior state := receive (fun _ => become st).

(* 初期状態 *)
(* toplevel アクター一つだけはちょっと強すぎるかもしれない？ *)
Inductive initial_config : config -> Prop :=
| init_conf : forall machine actions,
    initial_config ([:: {|
                         actor_name := toplevel machine;
                         state_type := unit;
                         remaining_actions := actions;
                         next_num := 0;
                         behv := fun _ => receive (fun _ => actions);
                         queue := [::]
                       |}]).

Hint Constructors initial_config.

(* initial config を作るやつ *)
Definition init (sys_name : string) (actions : actions unit) : config :=
  [::
     {|
       actor_name := toplevel sys_name;
       state_type := unit;
       remaining_actions := actions;
       next_num := 0;
       behv := fun _ => receive (fun _ => actions);
       queue := [::]
     |}].

Lemma init_is_initial_config :
  forall sys_name behv,
    initial_config (init sys_name behv).
Proof.
  move=> sys_name behv.
  constructor.
Qed.
