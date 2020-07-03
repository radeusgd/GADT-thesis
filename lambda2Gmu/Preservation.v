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

Lemma term_through_subst : forall e x u,
    term u ->
    term e ->
    term (subst_ee x u e).
  introv Htermu Hterme.
  induction e; eauto;
    try solve [
          cbn; case_if; eauto
        | inversion Hterme; subst; cbn; econstructor; eauto
        ].
  - cbn.
    econstructor; eauto.
    inversion Hterme; subst; eauto.
    inversion Hterme; subst; eauto.
    admit.
  - cbn. inversion Hterme; subst.
    econstructor.
    + intros; eauto.
Admitted.


Hint Resolve okt_is_ok.

Lemma wft_weaken : forall Σ E F G T,
    wft Σ (E & G) T ->
    ok (E & F & G) ->
    wft Σ (E & F & G) T.
  intros. gen_eq K: (E & G). gen E F G.
  induction H; intros; subst; auto.
  (* case: var *)
  apply (@wft_var Σ (E0 & F & G) X).  apply* binds_weaken.
  (* case: all *)
  apply_fresh* wft_all as X. apply_ih_bind* H0.
Qed.

Lemma wft_strengthen : forall Σ E F x U T,
 wft Σ (E & (x ~: U) & F) T -> wft Σ (E & F) T.
Proof.
  intros. gen_eq G: (E & (x ~: U) & F). gen F.
  induction H; intros F EQ; subst; auto.
  apply* (@wft_var).
  destruct (binds_concat_inv H) as [?|[? ?]].
    apply~ binds_concat_right.
    destruct (binds_push_inv H1) as [[? ?]|[? ?]].
      subst. false.
      apply~ binds_concat_left.
  (* todo: binds_cases tactic *)
  apply_fresh* wft_all as Y. apply_ih_bind* H0.
Qed.

(** ** Environment is unchanged by substitution from a fresh name *)

Lemma notin_fv_tt_open : forall Y X T,
  X \notin fv_typ (T open_tt_var Y) ->
  X \notin fv_typ T.
Proof.
 introv. unfold open_tt. generalize 0.
 induction T; simpl; intros k Fr; auto.
 specializes IHT1 k. specializes IHT2 k. auto.
 specializes IHT1 k. specializes IHT2 k. auto.
 eauto.
Qed.

Lemma notin_fv_wf : forall Σ E X T,
  wft Σ E T -> X # E -> X \notin fv_typ T.
Proof.
  induction 1; intros Fr; simpl.
  eauto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H Fr.
  notin_simpl; auto.
  notin_simpl; auto. pick_fresh Y. apply* (@notin_fv_tt_open Y).
Qed.

Lemma typing_weakening : forall Σ E F G e T,
   {Σ, E & G} ⊢ e ∈ T ->
   okt Σ (E & F & G) ->
   {Σ, E & F & G} ⊢ e ∈ T.
Proof.
  introv HTyp. gen F. inductions HTyp; introv Ok; eauto.
  - apply* typing_var. apply* binds_weaken.
  - apply_fresh* typing_abs as x.
    forwards~ K: (H x).
    apply_ih_bind (H0 x); eauto.
    econstructor; eauto.
    apply* wft_weaken.
    apply* wft_weaken.
  - apply_fresh* typing_tabs as X.
    forwards~ K: (H X).
    apply_ih_bind (H1 X).
    eauto. auto.
    econstructor; eauto.
  - apply* typing_tapp. apply* wft_weaken.
  - apply_fresh typing_let as x.
    eauto.
    apply wft_weaken. exact H.
    eauto.
    intros.
    forwards~ K: (H0 x); eauto.
    apply_ih_bind (H1 x); eauto.
    econstructor; eauto.
    apply* wft_weaken.
Qed.

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
  introv Htyp.
  assert (term e) as Hterm; eauto using typing_implies_term.
  generalize e'.
  clear e'.
  induction Htyp; inversion Hterm; subst;
    introv; intro Hred; inversion Hred; subst;
      try solve [crush_ihred_gen | eauto].
  - inversion Htyp2; subst.
    pick_fresh x.
    assert (x \notin L) as HxiL; eauto.
    lets Hbind: (H8 x HxiL).
    admit.
  - admit.
  - inversion Htyp; inversion Hterm; subst; eauto.
  - inversion Htyp; inversion Hterm; subst; eauto.
  - admit.
Admitted.
