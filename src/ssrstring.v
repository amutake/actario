Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Strings.String.
Require Import ssreflect mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrbool.
Require Import ssrascii.

Section EqString.
  Fixpoint eqstring (s1 s2 : string) : bool :=
    match s1, s2 with
      | EmptyString, EmptyString => true
      | String a1 s1', String a2 s2' => (a1 == a2) && eqstring s1' s2'
      | _, _ => false
    end.

  Lemma eqstringP : Equality.axiom eqstring.
  Proof.
    elim=> [|a1 s1 IHs] [|a2 s2]; do [by constructor | simpl].
    case: (a1 =P a2) => [<-|?]; last by (right; case).
      by apply: (iffP (IHs s2)) => [<-|[]].
  Qed.

  Canonical string_eqMixin := EqMixin eqstringP.
  Canonical string_eqType := Eval hnf in EqType string string_eqMixin.
End EqString.
