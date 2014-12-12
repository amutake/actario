Set Implicit Arguments.
Unset Strict Implicit.

Require Import String List Relations.
Import ListNotations.

Require Import syntax.

Definition interp (m : message) (b : behavior) : list action :=
  match b with
    | beh f => f m
  end.

(* External Actor へのメッセージだったら???? (現状では configuration に宛先がいない場合はそこで遷移できなくなる) *)
(* アトミックではない (新しいメッセージと新しいアクターと新しい振る舞いを返すようにする？) *)
(* メッセージは必ず送信順に受け取られる？ *)
Inductive dispatch : sending -> list actor -> list actor -> Prop :=
| dispatch_in : forall addr content actions behv number actors_l actors_r,
                  interp content behv = actions ->
                  dispatch (send_message addr content)
                           (actors_l ++ actor_state addr [] behv number :: actors_r)
                           (actors_l ++ actor_state addr actions behv number :: actors_r).

(* send_action msg actors actors': actors が msg を送って actors' になる *)
Inductive send_action : sending -> list actor -> list actor -> Prop :=
| send_action_in : forall addr content addr' actions behv number actors_l actors_r,
                     send_action (send_message addr content)
                                 (actors_l ++ actor_state addr' (send addr content :: actions) behv number :: actors_r)
                                 (actors_l ++ actor_state addr' actions behv number :: actors_r).

(* new_action actor actors actors': actors が actor を生成して actors' になる *)
(* 新しく生成されたアクターは actors' の中に含まれない *)
Inductive new_action : actor -> list actor -> list actor -> Prop := (* new_action : list actor -> list actor -> Prop ??? *)
| new_action_in : forall new_beh cont parent actions behv number actors_l actors_r,
                    new_action (actor_state (generated parent number) [] new_beh 0)
                               (actors_l ++ actor_state parent (new new_beh cont :: actions) behv number :: actors_r)
                               (actors_l ++ actor_state parent (cont (generated parent number) ++ actions) behv (S number) :: actors_r).

(* new_become actors actors': actors のなかのどれかが become アクションを実行して actors' になる *)
Inductive become_action : list actor -> list actor -> Prop :=
| become_action_in : forall new_beh old_beh addr actions number actors_l actors_r,
                       become_action (actors_l ++ actor_state addr (become new_beh :: actions) old_beh number :: actors_r)
                                     (actors_l ++ actor_state addr actions new_beh number :: actors_r).

Inductive trans_type := Dispatch | Send | New | Become.

(* relation config *)
(* trans conf conf': conf が遷移して conf' になる *)
Inductive trans : trans_type -> config -> config -> Prop :=
| trans_dispatch : forall msg msgs actors actors',
                     dispatch msg actors actors' ->
                     trans Dispatch (conf (msg :: msgs) actors) (conf msgs actors')
| trans_send_action : forall msg msgs actors actors',
                        send_action msg actors actors' ->
                        trans Send
                              (conf msgs actors)
                              (conf (msgs ++ [msg]) actors')
| trans_new_action : forall msgs new_actor actors actors',
                       new_action new_actor actors actors' ->
                       trans New
                             (conf msgs actors)
                             (conf msgs (new_actor :: actors'))
| trans_become_action : forall msgs actors actors',
                          become_action actors actors' ->
                          trans Become
                                (conf msgs actors)
                                (conf msgs actors').

Hint Constructors trans.

Inductive trans_star : config -> config -> Prop :=
| trans_refl : forall c, trans_star c c
| trans_trans : forall c1 c2 c3, (forall t, trans t c1 c2) -> trans_star c2 c3 -> trans_star c1 c3.

Hint Constructors trans_star.
