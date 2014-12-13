Set Implicit Arguments.
Unset Strict Implicit.

Require Import String List.
Import ListNotations.

Require Import syntax.

Definition interp (m : message) (b : behavior) : actions :=
  match b with
    | beh f => f m
  end.

Inductive trans_type := Deliver | Open | Send | New | Self.

(* relation config *)
(* trans type conf conf': type という遷移の種類で conf が遷移して conf' になる *)
Inductive trans : trans_type -> config -> config -> Prop :=

(* グローバルキューから、アクターのメッセージキューにメッセージを届ける *)
(* External Actor へのメッセージだったら? (現状では configuration に宛先がいない場合はそこで遷移できなくなる) *)
(* external_deliver というコンストラクタを追加するとか？=> そうなると configuration 同士をまとめるような configuration になるのでどう定義すればいいのかわからないし、変更するならかなり大規模な変更になりそう *)
| trans_deliver : forall global_queue addr msg actions queue number actors_l actors_r,
                    trans Deliver
                          (conf (send_message addr msg :: global_queue)
                                (actors_l
                                   ++ actor_state addr actions queue number
                                   :: actors_r))
                          (conf global_queue
                                (actors_l
                                   ++ actor_state addr actions (queue ++ [msg]) number
                                   :: actors_r))

(* メッセージキューの先頭からメッセージを開封 *)
(* deliver と合わせると、メッセージは必ず送信順に受け取られてしまうけど、いい？ *)
(* 無限ループ以外は become 以外最後にならないので、become が来てたらもう他にアクションを起こさないから次のメッセージを受け取れる *)
| trans_open : forall global_queue addr behv msg queue number actors_l actors_r,
                 trans Open
                       (conf global_queue
                             (actors_l
                                ++ actor_state addr (become behv) (msg :: queue) number
                                :: actors_r))
                       (conf global_queue
                             (actors_l
                                ++ actor_state addr (interp msg behv) queue number
                                :: actors_r))
(* send アクションが出てきたら、グローバルキューの最後にそのメッセージを追加 *)
| trans_send : forall global_queue target msg addr cont queue number actors_l actors_r,
                 trans Send
                       (conf global_queue
                             (actors_l
                                ++ actor_state addr (send target msg cont) queue number
                                :: actors_r))
                       (conf (global_queue ++ [send_message target msg])
                             (actors_l
                                ++ actor_state addr cont queue number
                                :: actors_r))

| trans_new : forall global_queue addr behv cont queue number actors_l actors_r,
                trans New
                      (conf global_queue
                            (actors_l
                               ++ actor_state addr (new behv cont) queue number
                               :: actors_r))
                      (conf global_queue
                            (actor_state (generated addr number) (become behv) [] 0 (* 最初は become behv で待ち状態 *)
                               :: actors_l
                               ++ actor_state addr (cont (generated addr number)) queue (S number)
                               :: actors_r))

| trans_self : forall global_queue addr cont queue number actors_l actors_r,
                 trans Self
                       (conf global_queue
                             (actors_l
                                ++ actor_state addr (self cont) queue number
                                :: actors_r))
                       (conf global_queue
                             (actors_l
                                ++ actor_state addr (cont addr) queue number
                                :: actors_r)).

Hint Constructors trans.

Inductive trans_star : config -> config -> Prop :=
| trans_refl : forall c, trans_star c c
| trans_trans : forall c1 c2 c3, (forall t, trans t c1 c2) -> trans_star c2 c3 -> trans_star c1 c3.

Hint Constructors trans_star.
