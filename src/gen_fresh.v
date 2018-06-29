Set Implicit Arguments.
Unset Strict Implicit.

Require Import ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat.
Require Import Coq.Program.Equality Coq.Bool.Bool Coq.Sorting.Permutation.
Require Import util syntax semantics name_dec chain.

Definition name_next (a : actor) := (actor_name a, next_num a).

Definition gen_fresh (c : config) :=
  forall parent_name parent_next,
    (parent_name, parent_next) \in [seq name_next i | i <- c] ->
    forall child_gen,
      (generated child_gen parent_name) \in [seq actor_name i | i <- c] ->
      child_gen < parent_next.

Theorem gen_fresh_soundness :
  forall c n x,
    gen_fresh c ->
    (n, x) \in [seq name_next i | i <- c] ->
    generated x n \notin [seq actor_name i | i <- c].
Proof.
  move=> c n x.
  rewrite/gen_fresh.
  move/(_ n x)=> fr inp.
  apply/negP=> contra.
  move/(_ inp x contra): fr.
  by rewrite ltnn.
Qed.

Lemma perm_gen_fresh :
  forall c c',
    Permutation c c' ->
    gen_fresh c ->
    gen_fresh c'.
Proof.
  move=> c c' perm.
  rewrite/gen_fresh.
  move=> H parent_name parent_next parent_in child_gen child_in.
  apply (perm_map_in (Permutation_sym perm)) in child_in.
  apply (perm_map_in (Permutation_sym perm)) in parent_in.
  by move/(_ parent_name parent_next parent_in child_gen child_in): H.
Qed.

Lemma gen_fresh_increase :
  forall parent_st parent_name parent_next
         parent_actions parent_behv parent_queue
         parent_actions' parent_behv' parent_queue'
         rest,
    gen_fresh ({|
                  state_type := parent_st;
                  actor_name := parent_name;
                  remaining_actions := parent_actions;
                  next_num := parent_next;
                  behv := parent_behv;
                  queue := parent_queue
                |} :: rest) ->
    gen_fresh ({|
                  state_type := parent_st;
                  actor_name := parent_name;
                  remaining_actions := parent_actions';
                  next_num := parent_next.+1;
                  behv := parent_behv';
                  queue := parent_queue'
                |} :: rest).
Proof.
  move=> parent_st parent_name parent_next
                   parent_actions parent_behv parent_queue
                   parent_actions' parent_behv' parent_queue'
                   rest.
  rewrite/gen_fresh/name_next/=.
  move=> H pn px parent_in child_gen child_in; subst.
  move: parent_in; rewrite in_cons.
  case/orP.
  - case/eqP => ? ?; subst.
    move/(_ parent_name parent_next _ child_gen child_in): H=> H.
    by apply/ltnW/H; apply/orP; left.
  - move=> ppin.
    move/(_ pn px _ child_gen child_in): H; apply.
    by apply/orP; right.
Qed.

Lemma gen_fresh_head :
  forall a c,
    gen_fresh (a :: c) ->
    generated (next_num a) (actor_name a) \notin [seq actor_name i | i <- (a :: c)].
Proof.
  move=> a c fr.
  move/(_ (a :: c) (actor_name a) (next_num a) fr): gen_fresh_soundness; apply.
  by apply/orP; left.
Qed.

Lemma perm_name_next_to_name :
  forall c c',
    Permutation (map name_next c) (map name_next c') ->
    Permutation (map actor_name c) (map actor_name c').
Proof.
  move=> c c'.
  have map_name_next_to_name :
    forall c, map (fun p => p.1) (map name_next c) = map actor_name c
      by elim=>//; by move=> /= ? ? ->.
  move=> perm.
  move: perm_map.
  move/(_ _ _ _ _ (fun p => p.1) perm).
    by repeat rewrite map_name_next_to_name.
Qed.

Lemma gen_fresh_decided_by_only_name_next :
  forall c c',
    Permutation (seq.map name_next c) (seq.map name_next c') ->
    gen_fresh c ->
    gen_fresh c'.
Proof.
  move=> c c' perm.
  rewrite/gen_fresh/=.
  move=> fr parent_name parent_next parent_in child_gen child_in.
  move/(_ parent_name parent_next _ child_gen): fr; apply.
  - admit. (*by eapply (perm_in (Permutation_sym perm)).*)
  - have perm' : Permutation [seq actor_name i | i <- c] [seq actor_name i | i <- c']
      by apply perm_name_next_to_name.
    (*by eapply (perm_in (Permutation_sym perm')).*)
    admit.
Admitted.
