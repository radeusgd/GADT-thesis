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
Hint Extern 1 (ok _) => apply okt_is_ok.

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
Qed.

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

Lemma okt_implies_okgadt : forall Σ E, okt Σ E -> okGadt Σ.
  induction 1; auto.
Qed.

(* Lemma okt_strengthen : forall Σ E x U F, *)
(*     okt Σ (E & (x ~: U) & F) -> okt Σ (E & F). *)
(*   intros. *)
(*   assert (HGADT: okGadt Σ); eauto using okt_implies_okgadt. *)
(*   assert (HXF: x # F). apply okt_is_ok in H. lets HOMI: ok_middle_inv H. inversion* HOMI. *)
(*   gen_eq K: (E & (x ~: U) & F). gen E x U F. *)
(*   induction H; introv HXF EQ; subst; auto. *)
(*   - exfalso. *)
(*     assert (binds x (bind_var U) (E & x ~ bind_var U & F)); eauto. *)
(*     rewrite <- EQ in H0. *)
(*     apply* binds_empty_inv. *)
(* Admitted. *)

Lemma okt_strengthen_simple : forall Σ E x U,
    okt Σ (E & (x ~: U)) -> okt Σ E.
  intros.
  inversion H.
  - exfalso; apply* empty_push_inv.
  - apply eq_push_inv in H0. destruct H0 as [Ha [Hb Hc]].
    congruence.
  - apply eq_push_inv in H0. destruct H0 as [Ha [Hb Hc]]. subst*.
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
Hint Resolve typing_implies_term wft_strengthen.
Lemma typing_through_subst_ee : forall Σ E x u U e T,
    {Σ, E & (x ~: U)} ⊢ e ∈ T ->
    {Σ, E} ⊢ u ∈ U ->
    {Σ, E} ⊢ subst_ee x u e ∈ T.
(* Lemma typing_through_subst_ee : forall Σ E F x u U e T, *)
(*     {Σ, E & (x ~: U) & F} ⊢ e ∈ T -> *)
(*     {Σ, E} ⊢ u ∈ U -> *)
(*     {Σ, E & F} ⊢ subst_ee x u e ∈ T. *)
  (* introv TypT TypU. *)
  (* inductions TypT; introv; cbn; eauto. *)
  (* - assert (okt Σ (E & F)). eapply okt_strengthen; eauto. *)
  (*   case_var. *)
  (*   + binds_get H. eauto. *)
  (*     assert (E & F & empty = E & F) as HEF. apply concat_empty_r. *)
  (*     rewrite <- HEF. *)
  (*     apply typing_weakening; rewrite concat_empty_r; eauto. *)
  (*   + binds_cases H; apply* typing_var. *)
  (* - apply_fresh* typing_abs as y. *)
  (*   rewrite* subst_ee_open_ee_var. *)
  (*   apply_ih_bind* H0. *)
  (* - apply_fresh* typing_tabs as Y. *)
  (*   rewrite* subst_ee_open_te_var. *)
  (*   rewrite* subst_ee_open_te_var. *)
  (*   apply_ih_bind* H1. *)
  (* - apply_fresh* typing_let as y. *)
  (*   rewrite* subst_ee_open_ee_var. *)
  (*   apply_ih_bind* H1. *)


  introv TypT TypU.
  inductions TypT; introv; cbn; eauto.
  - case_var.
    + rewrite <- concat_empty_r in H.
      binds_get H. rewrite -> concat_empty_r. apply* okt_is_ok.
      auto.
    + binds_cases H; apply* typing_var.
      apply* okt_strengthen_simple.
  - apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply* H0.
    apply_ih_bind* H0.
    assert (HE: E & y ~ bind_var V = E & y ~ bind_var V & empty). rewrite* concat_empty_r.
    rewrite HE.
    apply_ih_bind* H0.
    rewrite concat_empty_
  - apply_fresh* typing_tabs as Y.
    rewrite* subst_ee_open_te_var.
    rewrite* subst_ee_open_te_var.
    apply_ih_bind* H1.
  - apply_fresh* typing_let as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H1.
Admitted.

(* Lemma typing_through_subst_te : forall Σ E F Z e T P, *)
(*   {Σ, E & (withtyp Z) & F} ⊢ e ∈ T -> *)
(*   {Σ, E & map (subst_tb Z P) F} ⊢ (subst_te Z P e) ∈ (subst_tt Z P T). *)
(* Proof. *)
(* Admitted. *)
Lemma typing_through_subst_te : forall Σ E Z e T P,
  {Σ, E & (withtyp Z)} ⊢ e ∈ T ->
  {Σ, E} ⊢ (subst_te Z P e) ∈ (subst_tt Z P T).
Proof.
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
  induction Htyp; inversions Hterm;
    introv; intro Hred; inversions Hred;
      try solve [crush_ihred_gen | eauto].
  - (* app *)
    inversions Htyp2.
    pick_fresh x. forwards~ K: (H8 x).
    rewrite* (@subst_ee_intro x).
    apply* typing_through_subst_ee.
    (* assert (HE: E = E & empty). rewrite* concat_empty_r. *)
    (* rewrite HE. *)
    (* apply* typing_through_subst_ee. *)
    (* assert (HEx: E & x ~ bind_var T1 = E & x ~ bind_var T1 & empty). rewrite* concat_empty_r. *)
    (* rewrite* <- HEx. *)
  - inversions Htyp.
    pick_fresh X. forwards~ K: (H9 X).
    rewrite* (@subst_te_intro X).
    rewrite* (@subst_tt_intro X).
    (* assert (HE: E = E & empty). rewrite* concat_empty_r. *)
    (* rewrite HE. *)
    (* apply typing_through_subst_te. *)
    (* assert (HEx: E & x ~ bind_var V = E & x ~ bind_var V & empty). rewrite* concat_empty_r. *)
    (* rewrite* <- HEx. *)
    apply* typing_through_subst_te.
  - inversion Htyp; subst; eauto.
  - inversion Htyp; subst; eauto.
  - (* let *)
    pick_fresh x. forwards~ K: (H0 x).
    rewrite* (@subst_ee_intro x).
    apply* typing_through_subst_ee.
Qed.
