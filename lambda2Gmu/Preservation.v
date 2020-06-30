Require Import Definitions.
Require Import Infrastructure.
Require Import CanonicalForms.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

Lemma okt_is_ok : forall Σ E, okt Σ E -> ok E.
  introv. intro Hokt.
  induction Hokt; eauto.
Qed.

Hint Resolve okt_is_ok.

Lemma wft_weakening : forall Σ E F G T,
    wft Σ (E & G) T ->
    okt Σ (E & F & G) ->
    wft Σ (E & F & G) T.
  introv.
  generalize E F G.
  induction T; intros; eauto;
    inversion H; subst.
  - econstructor; apply* binds_weaken.
  - econstructor.
    + eapply IHT1 in H5; eauto.
    + eapply IHT2 in H6; eauto.
  - econstructor.
    + eapply IHT1 in H5; eauto.
    + eapply IHT2 in H6; eauto.
  - econstructor.
    introv.
    intros HXiL.
    lets H_: (H4 X HXiL).
    (* lets H__: (IHT E0 F0 (G0 & X ~ bind_typ)). *)
    inversion H_; subst; eauto.
    admit.
Qed.

Lemma typing_weakening : forall Σ E F G e T,
   {Σ, E & G} ⊢ e ∈ T ->
   okt Σ (E & F & G) ->
   {Σ, E & F & G} ⊢ e ∈ T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok; eauto.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as x.
  admit.
  forwards~ K: (H0 x).
Admitted.

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
    admit.
  - admit.
  - inversion Htyp; inversion Hterm; subst; eauto.
    inversion H10; subst; eauto.
  - inversion Htyp; inversion Hterm; subst; eauto.
    inversion H10; subst; eauto.
Admitted.
