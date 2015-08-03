Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq Ssreflect.ssrnat.
Require Import syntax semantics util.

Section ActorPersistence.

  Ltac crash H :=
    rewrite map_cat /= mem_cat in_cons;
      by move: H; rewrite map_cat /= mem_cat in_cons.

  (* actors do not disappear *)
  Theorem actor_persistence :
    forall c c' l n,
      n \in map actor_name (actors c) ->
            c ~(l)~> c' ->
            n \in map actor_name (actors c').
  Proof.
    move=> c c' l n n_in_c tr.
    inversion tr; subst; simpl in *.
    - crash n_in_c.
    - crash n_in_c.
    - rewrite in_cons map_cat /= mem_cat in_cons; apply/or4P.
      move: n_in_c; rewrite map_cat /= mem_cat in_cons; move/or3P.
      case=> in_p.
      + by apply/Or42.
      + by apply/Or43.
      + by apply/Or44.
    - crash n_in_c.
  Qed.

End ActorPersistence.

Section MessagePersistence.

  (* messages do not disappear without received *)
  Theorem message_persistence :
    forall c c' l m (n : nat),
      n == count_mem m (sending_messages c) ->
      c ~(l)~> c' ->
      if l == Receive (sending_to m) (sending_from m) (sending_content m) then
        count_mem m (sending_messages c') == n.-1
      else
        if l == Send (sending_from m) (sending_to m) (sending_content m) then
          count_mem m (sending_messages c') == n.+1
        else
          count_mem m (sending_messages c') == n.
  Proof.
    move=> c c' l m n.
    case: l=> [ to fr co | fr to co | ch | me ];
      move=> n_eq tr; inversion tr; subst; simpl in *.
    - case m_eq : (Build_sending to fr co == m).
      + move: n_eq.
        move/eqP: m_eq=>m_eq.
        rewrite -m_eq /= m_eq.
        rewrite eq_refl.
        move/eqP=>->.
        rewrite 2!count_cat /=.
        rewrite eq_refl.
        rewrite add1n addnS /=.
        done.
      + have: (Receive to fr co ==
               Receive (sending_to m) (sending_from m) (sending_content m) = false).
        * apply/negP=>contra; move: contra m_eq; case/eqP.
          clear n_eq tr; case: m=> to' fr' co'; move=>/=->->->.
          rewrite eq_refl; done.
        * move=>->.
          move/eqP: n_eq=>->.
            by rewrite 2!count_cat /= m_eq /= add0n.
    - case m_eq : (Build_sending to fr co == m).
      + move: n_eq; move/eqP: m_eq=> m_eq.
        rewrite -m_eq /= m_eq.
        move/eqP=>->.
        rewrite eq_refl.
        rewrite 2!count_cat /= eq_refl.
          by rewrite add1n addnS.
      + have: (Send fr to co ==
               Send (sending_from m) (sending_to m) (sending_content m)) = false.
        * apply/negP=>contra; move: contra m_eq; case/eqP.
          clear n_eq tr; case: m=> to' fr' co'; move=>/=->->->.
            by rewrite eq_refl.
        * move=>->.
          move/eqP: n_eq=>->.
            by rewrite 2!count_cat /= m_eq /= add0n.
    - by move/eqP: n_eq=>->.
    - by move/eqP: n_eq=>->.
  Qed.
End MessagePersistence.
