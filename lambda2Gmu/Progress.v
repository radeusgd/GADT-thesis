Require Import Definitions.
Require Import Infrastructure.
Require Import CanonicalForms.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

Ltac fs := exact \{}. (* There must be a better way *)
Hint Resolve binds_empty_inv.

Ltac empty_binding :=
  match goal with
  | H: binds ?x ?v empty |- _ => apply binds_empty_inv in H; contradiction
  | _ => fail "no empty bindings found"
  end.

Lemma value_is_term : forall v,
    value v -> term v.
  induction 1; eauto.
Qed.

Lemma typed_is_term : forall Σ G T t,
    {Σ, G} ⊢ t ∈ T ->
    term t.
  induction 1; subst; eauto.
  - econstructor; eauto.
    intros.
    admit.
  - econstructor; eauto.
    inversion IHtyping; 
      admit.
Admitted.

Ltac IHT e :=
  match goal with
  | Ht: {?Σ, ?E} ⊢ e ∈ ?T |- _ =>
    match goal with
    | IH: forall T, {Σ, E} ⊢ e ∈ T -> ?P |- _ =>
      let H := fresh "IHt" in
      assert P as H; eauto
    end
  end.

Ltac copy H1 H2 :=
  let Heq := fresh "Heq" in
  remember H1 as H2 eqn:Heq; clear Heq.

Hint Constructors value red.
Theorem progress_thm : progress.
  unfold progress.
  intro.
  induction e; introv; intros Htyp; inversion Htyp; subst.
  - empty_binding.
  - IHT e1. IHT e2.
    destruct IHt as [IHv1 | IHev1].
    + destruct IHt0 as [IHv2 | IHev2].
      * left; eauto.
      * inversion IHev2 as [e2' Hev2].
        right; eauto.
    + inversion IHev1; right; eauto.
  - IHT e.
    destruct IHt as [Hv | Hev].
    copy Hv Hv'.
    eapply CanonicalFormTuple in Hv; eauto.
    inversion Hv as [v1 Hv2]; inversion Hv2 as [v2 Heq]; subst.
    right; eauto.

    inversion Hev as [e' ev]; eauto.
  - IHT e.
    destruct IHt as [Hv | Hev].
    copy Hv Hv'.
    eapply CanonicalFormTuple in Hv; eauto.
    inversion Hv as [v1 Hv2]; inversion Hv2 as [v2 Heq]; subst.
    right; eauto.

    inversion Hev as [e' ev]; eauto.
  - left; econstructor; econstructor; eauto.
    intros; eapply typed_is_term; eauto. (* TODO ? *)
  - IHT e1; IHT e2.
    destruct IHt as [Hv1 | Hev1].
    + destruct IHt0 as [Hv2 | Hev2].
      * copy Hv1 Hv1'.
        eapply CanonicalFormAbs in Hv1'; eauto.
        inversion Hv1' as [v1 Heq]; subst.
        right; eexists; econstructor; eauto.
        eapply typed_is_term; eauto.
      * right; inversion Hev2; eexists; eauto.
    + right; inversion Hev1; eexists; eauto.
  - left; econstructor; econstructor; eauto.
    inversion Htyp; subst. (*TODO *) admit.
  - IHT e.
    destruct IHt as [Hv | Hev].
    + right.
      copy Hv Hv'.
      eapply CanonicalFormTAbs in Hv'; eauto.
      inversion Hv' as [v1 eq]; subst.
      eexists. econstructor; eauto.
      admit.
      admit.
    + admit.
      Unshelve. fs.

Qed.
