Set Implicit Arguments.
Unset Strict Implicit.

Require Import Actor.syntax Actor.semantics.

(* 受け取ったメッセージを送ってきたアクターにそのまま返す *)
CoFixpoint echo_server_behavior : behavior :=
  mk_behv (fun msg =>
         match msg with
           | tuple_msg (name_msg sender) content =>
             sender ! content;
             become echo_server_behavior
           | _ => become echo_server_behavior
         end).

(* サーバに Hello! というメッセージを送り続ける *)
(* echo_server に送ったとき、ちゃんと Hello! が返ってきたことを確かめるには？ *)
CoFixpoint echo_client_behavior (server : name) : behavior :=
  mk_behv (fun _ =>
         me <- self;
         server ! (tuple_msg (name_msg me) (str_msg "Hello!"));
         become (echo_client_behavior server)
      ).

Definition echo_init_system : config :=
  init "echo-system" (
         server <- new echo_server_behavior; (* サーバーを作る *)
         client <- new (echo_client_behavior server); (* クライアントを作る *)
         client ! empty_msg; (* クライアントを走らせる *)
         become empty_behv (* それ以降は何もしない *)
       ).
