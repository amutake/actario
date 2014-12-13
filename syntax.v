Set Implicit Arguments.
Unset Strict Implicit.

Require Import String List Relations.
Import ListNotations.

Definition machine_addr := string.
Definition gen_number := nat.

Inductive name_type := Toplevel | Generated.

Inductive name : Set :=
| toplevel : machine_addr -> name
| generated : name -> gen_number -> name. (* ユーザーに generated というコンストラクタを使わせたくないのだけどできる？ *)

(* 任意の Set をメッセージとして送ることができるようにするなら、message と name と actor に型タグ付けないといけない (と思う) *)
(* Inductive message (A : Set) : Set := wrap : A -> message A. みたいに。じゃないとパターンマッチできない *)
Inductive message : Set :=
| empty_msg : message
| name_msg : name -> message
| str_msg : string -> message
| nat_msg : nat -> message
| bool_msg : bool -> message
| tuple_msg : message -> message -> message.

(* Behavior は自分を指定することがよくあるので、Inductive だと再帰が書けなくなるので、CoInductive にしている *)
CoInductive action : Type :=
| new : behavior -> (name -> action) -> action (* CPS *)
| send : name -> message -> action -> action   (* send n m a == n ! m;; a *)
| self : (name -> action) -> action            (* CPS *)
| become : behavior -> action                  (* become した後はアクションを取れない。become 以外は後に action が続かなければならないので、最後は必ず become になる *)
with behavior : Type :=
| beh : (message -> action) -> behavior.

Notation "n '<-' 'new' behv ; cont" := (new behv (fun n => cont)) (at level 0, cont at level 10).
Notation "n '!' m ';' a" := (send n m a) (at level 0, a at level 10).
Notation "me '<-' 'self' ';' cont" := (self (fun me => cont)) (at level 0, cont at level 10).

Inductive sending : Type := send_message : name -> message -> sending.

Inductive actor : Type :=
| actor_state : name -> action -> behavior -> gen_number -> actor.

Inductive config : Type :=
| conf : list sending -> list actor -> config.

(* メッセージを受け取っても何もしない振る舞い *)
CoFixpoint empty_behv : behavior := beh (fun _ => become empty_behv).

(* 初期状態 *)
(* toplevel アクター一つだけはちょっと強すぎるかもしれない？ *)
Inductive initial_config : config -> Prop :=
| init_conf : forall behv machine actions,
                initial_config (conf [] [actor_state (toplevel machine) actions behv 0]).

Hint Constructors initial_config.

(* initial config を作るやつ *)
Definition init (sys_name : string) (actions : action) : config :=
  conf [] [ actor_state (toplevel sys_name) actions empty_behv 0 ].

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

  Print echo_init_system.

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

  (* Parent name and Generated number with Prop *)
  Definition pgprop (a : actor) (P : name -> gen_number -> Prop) : Prop :=
    match a with
      | actor_state (generated pr nm) _ _ _ => P pr nm
      | _ => True
    end.

End Getter.

Module G := Getter.
