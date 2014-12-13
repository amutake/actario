Set Implicit Arguments.
Unset Strict Implicit.

Require Import String List Relations.
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
| send : name -> message -> actions -> actions   (* send n m a == n ! m;; a *)
| self : (name -> actions) -> actions            (* CPS *)
| become : behavior -> actions                   (* become した後はアクションを取れない。become 以外は後に actions が続かなければならないので、次のメッセージを受け取れる状態になれば必ず become になる *)
with behavior : Type :=
| beh : (message -> actions) -> behavior.

Notation "n '<-' 'new' behv ; cont" := (new behv (fun n => cont)) (at level 0, cont at level 10).
Notation "n '!' m ';' a" := (send n m a) (at level 0, a at level 10).
Notation "me '<-' 'self' ';' cont" := (self (fun me => cont)) (at level 0, cont at level 10).

(* Lemma "アクションに終わりがあるなら、アクションの最後は become しか来ない"
 * CoInductive なので action := send name msg action みたいなのが書けるから自明ではないんだけど、これ証明できるの？
 * become = "ある振る舞いでもって、次のメッセージの待ち状態になる" という意味だからいいのか
 *)

Inductive sending : Type := send_message : name -> message -> sending.

(* actor_state (このアクターの名前) (まだ実行していないアクション) (メッセージキュー) (生成番号) *)
Inductive actor : Type :=
| actor_state : name -> actions -> list message -> gen_number -> actor. (* behavior は持ってない。actions の最後に次の behavior が来るのと、アクションをし終わった (つまり become がでてきた) 状態のアクターしかメッセージを受け取れないので。でもこれはアクターとしてどうなの？外からは見えないものだけど。。 *)
(* あと、グローバルメッセージキューの他に actor もメッセージキューを持つようにしたい。グローバルキューだけだと、先頭のメッセージの宛先のアクターがいつまでたっても仕事が終わらないとき、他のアクターはメッセージを受け取れない *)

Inductive config : Type :=
| conf : list sending -> list actor -> config. (* config が list sending を持つメリットはある？External Actor への送信とか？ *)

(* メッセージを受け取っても何もしない振る舞い *)
CoFixpoint empty_behv : behavior := beh (fun _ => become empty_behv).

(* 初期状態 *)
(* toplevel アクター一つだけはちょっと強すぎるかもしれない？ *)
Inductive initial_config : config -> Prop :=
| init_conf : forall machine actions,
                initial_config (conf [] [actor_state (toplevel machine) actions [] 0]).

Hint Constructors initial_config.

(* initial config を作るやつ *)
Definition init (sys_name : string) (initial_actions : actions) : config :=
  conf [] [ actor_state (toplevel sys_name) initial_actions [] 0 ].

Lemma init_is_initial_config :
  forall sys_name actions,
    initial_config (init sys_name actions).
Proof.
  intros sys_name actions.
  unfold init.
  auto.
Qed.

(* Examples *)
Module NotationExamples.

  (* Notation のテスト *)
  Definition notation_test_behv : behavior :=
    beh (fun _ =>
           server <- new empty_behv;
           me <- self;
           server ! name_msg me;
           become empty_behv).

  (* 受け取ったメッセージを送ってきたアクターにそのまま返す *)
  CoFixpoint echo_server_behavior : behavior :=
    beh (fun msg =>
           match msg with
             | tuple_msg (name_msg sender) content =>
               sender ! content; become echo_server_behavior
             | _ => become echo_server_behavior
           end).

  (* サーバに Hello! というメッセージを送り続ける *)
  (* echo_server に送ったとき、ちゃんと Hello! が返ってきたことを確かめるには？ *)
  CoFixpoint echo_client_behavior (server : name) : behavior :=
    beh (fun _ =>
           me <- self;
           server ! (tuple_msg (name_msg me) (str_msg "Hello!"));
           become (echo_client_behavior server)
        ).

  Definition echo_init_system : config :=
    init "echo-system" (server <- new echo_server_behavior; (* サーバーを作る *)
                        client <- new (echo_client_behavior server); (* クライアントを作る *)
                        client ! empty_msg; (* クライアントを走らせる *)
                        become empty_behv). (* それ以降は何もしない *)

End NotationExamples.

Module Getter.

  (* Parent name *)
  Definition p (a : actor) : option name :=
    match a with
      | actor_state (generated parent _) _ _ _ => Some parent
      | _ => None
    end.

  (* State generation number *)
  Definition s (a : actor) : gen_number :=
    match a with
      | actor_state _ _ _ num => num
    end.

  (* Name *)
  Definition n (a : actor) : name :=
    match a with
      | actor_state nm _ _ _ => nm
    end.

  (* Generated number *)
  Definition g (a : actor) : option gen_number :=
    match a with
      | actor_state (generated _ gen) _ _ _ => Some gen
      | _ => None
    end.

  (* Parent name and Generated number *)
  Definition pg (a : actor) : option (name * gen_number) :=
    match a with
      | actor_state (generated p' g') _ _ _ => Some (p', g')
      | _ => None
    end.

  (* Name and State generation number *)
  Definition ns (a : actor) : (name * gen_number) :=
    match a with
      | actor_state n' _ _ s' => (n', s')
    end.

  (* Parent name with Prop *)
  Definition pprop (a : actor) (P : name -> Prop) : Prop :=
    match a with
      | actor_state (generated pr _) _ _ _ => P pr
      | _ => True
    end.

  (* Parent name with Prop from Name *)
  Definition pprop_n (n : name) (P : name -> Prop) : Prop :=
    match n with
      | toplevel _ => True
      | generated pr _ => P pr
    end.

  (* Parent name and Generated number with Prop *)
  Definition pgprop (a : actor) (P : name -> gen_number -> Prop) : Prop :=
    match a with
      | actor_state (generated pr nm) _ _ _ => P pr nm
      | _ => True
    end.

End Getter.

Module G := Getter.
