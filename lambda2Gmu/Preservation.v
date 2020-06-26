Require Import Definitions.
Require Import Infrastructure.
Require Import CanonicalForms.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.


Ltac IHR e :=
  match goal with
  | Hr: e --> ?e' |- _ =>
    match goal with
    | IH: term e -> ?P |- _ =>
      let H := fresh "IHRed" in
      eapply IH in Hr as H; eauto
    end
  end.

Ltac crush_ihred e :=
  IHR e; inversion IHRed; constructor; econstructor; eauto.

Ltac crush_ihred_gen :=
  match goal with
  | H: ?e --> ?e' |- _ =>
    crush_ihred e
  end.

Theorem preservation_thm : preservation.
  unfold preservation.
  introv.
  intros Hterm Htyp.
  generalize e'.
  clear e'.
  induction Htyp; inversion Hterm; subst;
    introv; intro Hred; inversion Hred; subst;
      try solve [crush_ihred_gen].
  - admit.
  - admit.
  - inversion Htyp; inversion Hterm; subst; eauto.
    inversion H10; subst; eauto.
  - inversion Htyp; inversion Hterm; subst; eauto.
    inversion H10; subst; eauto.
Admitted.
