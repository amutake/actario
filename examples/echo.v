Set Implicit Arguments.
Unset Strict Implicit.

Require Import Actario.syntax Actario.semantics.

(* 受け取ったメッセージを送ってきたアクターにそのまま返す *)
Definition server_behavior (state : unit) : behavior unit :=
  receive (fun msg =>
         match msg with
           | tuple_msg (name_msg sender) (str_msg "ping") =>
             sender ! (str_msg "pong");
             become state
           | _ => become state
         end).
(* これを Erlang に抽出すると以下のようになる。
 *
 * server_behavior(State) ->
 *     receive
 *         Msg ->
 *             case Msg of
 *                 {tuple_msg, {name_msg, Sender}, {str_msg, {...(means ping)}}} ->
 *                     Sender ! {...(means pong)},
 *                     server_behavior(State);
 *                 _ ->
 *                     server_behavior(State)
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

(* サーバに ping というメッセージを送る *)
Definition client_behavior (server_addr : name) : behavior name :=
  receive (fun _ =>
             me <- self;
             server_addr ! (tuple_msg (name_msg me) (str_msg "ping"));
             become server_addr
          ).

Definition pingpong_system : config :=
  init "pingpong" (
         server <- new server_behavior with tt; (* サーバーを作る *)
         client1 <- new client_behavior with server; (* クライアントを作る1 *)
         client2 <- new client_behavior with server; (* クライアントを作る2 *)
         client1 ! empty_msg; (* クライアントを走らせる1 *)
         client2 ! empty_msg;
         become done (* それ以降は何もしない *)
       ).

Recursive ActorExtraction empty_behv.
Recursive ActorExtraction server_behavior.
Recursive ActorExtraction client_behavior.
Recursive ActorExtraction pingpong_system.
ActorExtraction "pingpong.erl" pingpong_system.

Section Verification.
  Require Import Ssreflect.ssreflect Ssreflect.seq.
  Require Import Actario.fairness Actario.specification Actario.tactics.

  Definition top := toplevel "pingpong".
  Theorem receive_client1 :
    fairness ->
    eventually_receive pingpong_system (generated 1 top) (str_msg "pong").
  Proof.
    unfold_eventually eventually_receive.
    move=> fairness p p0 is_path.
    step is_path p0=> p1.
    step is_path p1=> p2.
    step is_path p2=> p3.
    step is_path p3=> p4.
    step is_path p4.
    case=> p5.
    - step is_path p5.
      case=> p6.
      - step is_path p6.
        admit.
      - admit.
    - admit.
  Qed.
