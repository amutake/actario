Set Implicit Arguments.
Unset Strict Implicit.

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq.
Require Import syntax semantics util.

Theorem actor_persistence :
  forall c c' l n,
      n \in map actor_name (actors c) ->
      c ~(l)~> c' ->
      n \in map actor_name (actors c').
Proof.
  move=> c c' l n n_in_c tr.
  inversion tr; subst; simpl in *.
  - rewrite map_cat /= mem_cat in_cons.
    by move: n_in_c; rewrite map_cat /= mem_cat in_cons.
  - rewrite map_cat /= mem_cat in_cons.
    by move: n_in_c; rewrite map_cat /= mem_cat in_cons.
  - rewrite in_cons map_cat /= mem_cat in_cons; apply/or4P.
    move: n_in_c; rewrite map_cat /= mem_cat in_cons; move/or3P.
    case=> in_p.
    + by apply/Or42.
    + by apply/Or43.
    + by apply/Or44.
  - rewrite map_cat /= mem_cat in_cons.
    by move: n_in_c; rewrite map_cat /= mem_cat in_cons.
Qed.

Theorem message_persistence :
  forall c c' l m,
    l != Receive (sending_to m) (sending_from m) (sending_content m) ->
    m \in sending_messages c ->
    c ~(l)~> c' ->
    m \in sending_messages c'.
Proof.
  move=> c c' l m.
  case: l=> [ to fr co | fr to co | ch | me ];
    move=> not_receive m_in_p tr; inversion tr; subst; simpl in *.
  - move: m_in_p.
    rewrite mem_cat /= in_cons; case/or3P=> in_p.
    + rewrite mem_cat; apply/orP; by left.
    + exfalso.
      move/negP: not_receive; apply.
      move/eqP: in_p=>-> /=.
      exact: eq_refl.
    + rewrite mem_cat; apply/orP; by right.
  - move: m_in_p.
    rewrite mem_cat; case/orP=> in_p.
    + rewrite mem_cat; apply/orP; by left.
    + rewrite mem_cat /= in_cons; apply/or3P; by apply Or33.
  - done.
  - done.
Qed.
