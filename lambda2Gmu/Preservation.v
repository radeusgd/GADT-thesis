Require Import Definitions.
Require Import Infrastructure.
Require Import CanonicalForms.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.


Lemma typing_through_subst_ee : forall Σ E F x u U e T,
    {Σ, E & (x ~: T) & F} ⊢ e ∈ T ->
    {Σ, E} ⊢ u ∈ U ->
    {Σ, E & F} ⊢ subst_ee x u e ∈ T.
  admit.
Admitted.

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
  - inversion Htyp2; subst.
    pick_fresh x.
    assert (x \notin L) as HxiL; eauto.
    lets Hbind: (H10 x HxiL).

  - admit.
  - inversion Htyp; inversion Hterm; subst; eauto.
    inversion H10; subst; eauto.
  - inversion Htyp; inversion Hterm; subst; eauto.
    inversion H10; subst; eauto.
Admitted.
