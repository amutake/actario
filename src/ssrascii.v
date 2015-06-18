Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Strings.Ascii.
Require Import Ssreflect.ssreflect Ssreflect.eqtype Ssreflect.ssrbool.

Section EqAscii.
  Definition eqascii (a a' : ascii) : bool :=
    match a, a' with
      | Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii b0' b1' b2' b3' b4' b5' b6' b7' =>
        (b0 == b0') && (b1 == b1') && (b2 == b2') && (b3 == b3') &&
                    (b4 == b4') && (b5 == b5') && (b6 == b6') && (b7 == b7')
    end.

  (* Thank you @hogekura san: https://gist.github.com/hogekura/cc6cbb16a6204f36b717 *)
  Lemma eqasciiP : Equality.axiom eqascii.
  Proof.
    move=> [? ? ? ? ? ? ? ?] [? ? ? ? ? ? ? ?].
    move H: (eqascii _ _) => []; constructor; move: H => /=;
    [ repeat move/andP=> [] | repeat move/nandP=> [|] ]; repeat move/eqP=> ?; congruence.

    (* Alternative proof (a bit slow) *)
    (* move=> [b0 b1 b2 b3 b4 b5 b6 b7] [b0' b1' b2' b3' b4' b5' b6' b7']. *)
    (* move: b0 b0' b1 b1' b2 b2' b3 b3' b4 b4' b5 b5' b6 b6' b7 b7'. *)
    (* repeat (do 2 case; try (by constructor)). *)
  Qed.

  Canonical ascii_eqMixin := EqMixin eqasciiP.
  Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.
End EqAscii.
