Declare ML Module "actor_extraction_plugin".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import String Coq.Lists.List.
Import ListNotations.

Definition machine_addr := string.
Definition gen_number := nat.

Inductive name : Set :=
| toplevel : machine_addr -> name
| generated : name -> gen_number -> name. (* ユーザーに generated というコンストラクタを使わせたくないのだけどできる？ *)

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

(* behavior は become で自分を指定することがよくあり、Inductive だとそのような再帰が書けなくなるので、CoInductive にしている *)
(* CoInductive なので、無限ループが書けちゃう *)
(* Inductive actions, CoInductive behavior な気がするけど、相互(余)帰納型でそういうのって書ける(正しい)の？ *)
(* CoFixpoint actions_example : actions :=
 *   let behv := beh (fun _ => actions_example) in
 *   become behv
 * とかするから、actions も CoInductive で良さそう
 *)
CoInductive actions : Type :=
| new : behavior -> (name -> actions) -> actions (* CPS *)
| send : name -> message -> actions -> actions   (* send n m a == n ! m; a *)
| self : (name -> actions) -> actions            (* CPS *)
| become : behavior -> actions                   (* become した後はアクションを取れない。become 以外は後に actions が続かなければならないので、次のメッセージを受け取れる状態になれば必ず become になる *)
with behavior : Type :=
| receive : (message -> actions) -> behavior.

Notation "n '<-' 'new' behv ; cont" := (new behv (fun n => cont)) (at level 0, cont at level 10).
Notation "n '!' m ';' a" := (send n m a) (at level 0, a at level 10).
Notation "me '<-' 'self' ';' cont" := (self (fun me => cont)) (at level 0, cont at level 10).

(* Lemma "アクションに終わりがあるなら、アクションの最後は become しか来ない"
 * CoInductive なので action := send name msg action みたいなのが書けるから自明ではないんだけど、これ証明できるの？
 * become = "ある振る舞いでもって、次のメッセージの待ち状態になる" という意味だからいいのか
 *)

Record sending := mkSending {
                      sending_to : name;
                      sending_from : name;
                      sending_content : message
                    }.

(* actor_state (このアクターの名前) (まだ実行していないアクション) (メッセージキュー) (生成番号) *)
Inductive actor := mkActor {
                       actor_name : name;
                       remaining_actions : actions;
                       next_num : gen_number
                     }.
(* behavior は持ってない。actions の最後に次の behavior が来るのと、アクションをし終わった (つまり become がでてきた) 状態のアクターしかメッセージを受け取れないので。でもこれはアクターとしてどうなの？外からは見えないものだけど。。 *)
(* あと、グローバルメッセージキューの他に actor もメッセージキューを持つようにしたい。グローバルキューだけだと、先頭のメッセージの宛先のアクターがいつまでたっても仕事が終わらないとき、他のアクターはメッセージを受け取れない -> configuration の中のメッセージの順番をなくせばOK *)

Inductive config := mkConfig {
                        sending_messages : list sending;
                        actors : list actor
                      }.
(* config が list sending を持つメリットはある？External Actor への送信とか？ -> アクターとしては一般的な定義 *)

(* メッセージを受け取っても何もしない振る舞い *)
CoFixpoint empty_behv : behavior := receive (fun _ => become empty_behv).

(* 初期状態 *)
(* toplevel アクター一つだけはちょっと強すぎるかもしれない？ *)
Inductive initial_config : config -> Prop :=
| init_conf : forall machine actions,
                initial_config (mkConfig [] [mkActor (toplevel machine) actions 0]).

Hint Constructors initial_config.

(* initial config を作るやつ *)
Definition init (sys_name : string) (initial_actions : actions) : config :=
  mkConfig [] [ mkActor (toplevel sys_name) initial_actions 0 ].

Lemma init_is_initial_config :
  forall sys_name actions,
    initial_config (init sys_name actions).
Proof.
  intros sys_name actions.
  unfold init.
  auto.
Qed.
