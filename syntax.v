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

Inductive message : Type := wrap : forall A : Set, A -> message. (* put in an envelop *)

Inductive action : Type :=
| new : behavior -> (name -> list action) -> action (* 継続渡し。ユーザーが生成する名前を直接指定できないようにする *)
| send : name -> message -> action
| become : behavior -> action (* これはシンタックスということを忘れない！！ *)
with behavior : Type :=
| beh : (message -> list action) -> behavior.

Inductive sending : Type := send_message : name -> message -> sending.

Inductive actor : Type :=
| actor_state : name -> list action -> behavior -> gen_number -> actor.

Inductive config : Type :=
| conf : list sending -> list actor -> config.


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
