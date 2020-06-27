Require Import Predefs.
Require Import TLC.LibTactics.

(* lemma from https://stackoverflow.com/q/27322979/1296238 *)
Lemma ex_falso: forall T: Type, False -> T.
  inversion 1.
Qed.

Definition translator : translation_type.
  unfold translation_type.
  intro.
  induction t; introv; intros okGadt Htyp.
  - apply ex_falso. inversion Htyp.
  - apply ex_falso. inversion Htyp; subst.
    admit.
  - admit.
  - econstructor.
Admitted.
