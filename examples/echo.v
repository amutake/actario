Set Implicit Arguments.
Unset Strict Implicit.

Require Import Actor.syntax Actor.semantics.

(* 受け取ったメッセージを送ってきたアクターにそのまま返す *)
CoFixpoint echo_server_behavior : behavior :=
  receive (fun msg =>
         match msg with
           | tuple_msg (name_msg sender) content =>
             sender ! content;
             become echo_server_behavior
           | _ => become echo_server_behavior
         end).
(* これを Erlang に抽出すると以下のようになる。
 *
 * echo_server_behavior() ->
 *     receive
 *         Msg ->
 *             case Msg of
 *                 {tuple_msg, {name_msg, Sender}, Content} ->
 *                     Sender ! Content,
 *                     echo_server_behavior();
 *                 _ ->
 *                     echo_server_behavior()
 *             end
 *     end.
 *
 * タプルのタグは必要。無かったら、name_msg とか str_msg とかの区別がつかない
 *
 * after (timeout のこと) については今はとりあえず考えないけど、絶対必要になる。実装するとしたら receive の引数にタイムアウトまで時間とその場合のアクションを書く感じになると思う。
 * ただ Coq で時間の概念をどう扱えばいいのかわからない。
 * 何秒とかに関わらず、メッセージがキューに無かったら非決定的にいつでもタイムアウトの遷移になりうるとか？
 * それとも意味があるのか微妙だけどステップ数を msec にするとか
 *)

(* サーバに Hello! というメッセージを送り続ける *)
(* echo_server に送ったとき、ちゃんと Hello! が返ってきたことを確かめるには？ *)
CoFixpoint echo_client_behavior (server : name) : behavior :=
  receive (fun _ =>
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

ActorExtraction echo_server_behavior.
ActorExtraction echo_client_behavior.
ActorExtraction echo_init_system.
