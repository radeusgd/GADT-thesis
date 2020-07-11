Set Implicit Arguments.
Require Import Definitions.
Require Import Infrastructure.
Require Import CanonicalForms.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

Ltac expand_env_empty E :=
  let HE := fresh "HE" in
  assert (HE: E = E & empty); [
    rewrite* concat_empty_r
  | rewrite HE ].

Ltac fold_env_empty :=
  match goal with
  | |- context [?E & empty] =>
    let HE := fresh "HE" in
    assert (HE: E = E & empty); [
      rewrite* concat_empty_r
    | rewrite* <- HE ]
  end.

Ltac fold_env_empty_H :=
  match goal with
  | H: context [?E & empty] |- _ =>
    let HE := fresh "HE" in
    assert (HE: E = E & empty); [
      rewrite* concat_empty_r
    | rewrite* <- HE in H]
  | H: context [empty & ?E] |- _ =>
    let HE := fresh "HE" in
    assert (HE: E = empty & E); [
      rewrite* concat_empty_l
    | rewrite* <- HE in H]
  end.

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

Lemma wft_type : forall Σ E T,
    wft Σ E T -> type T.
Proof.
  induction 1; eauto.
Qed.

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

Lemma okt_push_var_inv : forall Σ E x T,
  okt Σ (E & x ~: T) -> okt Σ E /\ wft Σ E T /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&?&?): (eq_push_inv H). false.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
Qed.

Lemma okt_push_typ_inv : forall Σ E X,
  okt Σ (E & withtyp X) -> okt Σ E /\ X # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. inverts~ M.
    lets (?&?&?): (eq_push_inv H). false.
Qed.

Lemma okt_push_inv : forall Σ E X B,
  okt Σ (E & X ~ B) -> B = bind_typ \/ exists T, B = bind_var T.
Proof.
  introv O. inverts O.
  false* empty_push_inv.
  lets (?&?&?): (eq_push_inv H). subst*.
  lets (?&?&?): (eq_push_inv H). subst*.
Qed.

Lemma okt_strengthen : forall Σ E x U F,
    okt Σ (E & (x ~: U) & F) -> okt Σ (E & F).
  introv O. induction F using env_ind.
  - rewrite concat_empty_r in *. lets*: (okt_push_var_inv O).
  - rewrite concat_assoc in *.
    lets Hinv: okt_push_inv O; inversions Hinv.
    + lets (?&?): (okt_push_typ_inv O).
      applys~ okt_sub.
    + inversions H.
      lets (?&?&?): (okt_push_var_inv O).
      applys~ okt_typ. applys* wft_strengthen.
Qed.

Lemma wft_subst_tb : forall Σ F E Z P T,
  wft Σ (E & (withtyp Z) & F) T ->
  wft Σ E P ->
  ok (E & map (subst_tb Z P) F) ->
  wft Σ (E & map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  introv WT WP. gen_eq G: (E & (withtyp Z) & F). gen F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt; auto.
  case_var*.
  (*   apply_empty* wft_weaken. *)
  (*   destruct (binds_concat_inv H) as [?|[? ?]]. *)
  (*     apply (@wft_var (subst_tt Z P U)).  *)
  (*      apply~ binds_concat_right.  *)
  (*      unsimpl_map_bind. apply~ binds_map. *)
  (*     destruct (binds_push_inv H1) as [[? ?]|[? ?]]. *)
  (*       subst. false~. *)
  (*       applys wft_var. apply* binds_concat_left. *)
  (* apply_fresh* wft_all as Y.  *)
  (*  unsimpl ((subst_tb Z P) (bind_sub T1)). *)
  (*  lets: wft_type. *)
  (*  rewrite* subst_tt_open_tt_var. *)
  (*  apply_ih_map_bind* H0. *)
Admitted.

Hint Resolve wft_subst_tb.

Lemma okt_subst_tb : forall Σ Z P E F,
  okt Σ (E & (withtyp Z) & F) ->
  wft Σ E P ->
  okt Σ (E & map (subst_tb Z P) F).
Proof.
  introv O W. induction F using env_ind.
  - rewrite map_empty. rewrite concat_empty_r in *.
    lets*: (okt_push_typ_inv O).
  - rewrite map_push. rewrite concat_assoc in *.
    lets HPI: okt_push_inv O; destruct HPI; subst.
    + lets (?&?): (okt_push_typ_inv O).
      applys~ okt_sub.
    + inversions H.
      lets (?&?&?): (okt_push_var_inv O).
      applys~ okt_typ. applys* wft_subst_tb.
Qed.

(* Lemma ok_subst_tb : forall Σ Z P E F, *)
(*   ok (E & (withtyp Z) & F) -> *)
(*   wft Σ E P -> *)
(*   ok (E & map (subst_tb Z P) F). *)
(* Proof. *)
(*   introv O W. induction F using env_ind. *)
(*   - rewrite map_empty. rewrite concat_empty_r in *. *)
(*     inversions O. exfalso; apply* empty_push_inv. *)
(*     apply eq_push_inv in H. destructs H. subst*. *)
(*   - rewrite map_push. rewrite concat_assoc in *. *)

(*     lets HPI: okt_push_inv O; destruct HPI; subst. *)
(*     + lets (?&?): (okt_push_typ_inv O). *)
(*       applys~ okt_sub. *)
(*     + inversions H. *)
(*       lets (?&?&?): (okt_push_var_inv O). *)
(*       applys~ okt_typ. applys* wft_subst_tb. *)
(* Qed. *)

Lemma okt_strengthen_simple : forall Σ E F,
    okt Σ (E & F) -> okt Σ E.
  introv O.
  induction F using env_ind.
  - fold_env_empty_H.
  - rewrite concat_assoc in O.
    inversions O.
    + exfalso; apply* empty_push_inv.
    + apply eq_push_inv in H. destructs H; subst. auto.
    + apply eq_push_inv in H. destructs H; subst. auto.
Qed.

Hint Resolve okt_strengthen_simple.

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

Lemma map_subst_tb_id : forall Σ G Z P,
  okt Σ G -> Z # G -> G = map (subst_tb Z P) G.
Proof.
  induction 1; intros Fr; autorewrite with rew_env_map; simpl.
  - auto.
  - rewrite* <- IHokt.
  - rewrite* <- IHokt.
    rewrite* subst_tt_fresh.
    apply* notin_fv_wf.
Qed.

Hint Resolve map_subst_tb_id.

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

Lemma typing_through_subst_ee : forall Σ E F x u U e T,
    {Σ, E & (x ~: U) & F} ⊢ e ∈ T ->
    {Σ, E} ⊢ u ∈ U ->
    {Σ, E & F} ⊢ subst_ee x u e ∈ T.
  introv TypT TypU.
  inductions TypT; introv; cbn; eauto.
  - assert (okt Σ (E & F)). apply* okt_strengthen.
    case_var.
    + binds_get H. eauto.
      assert (E & F & empty = E & F) as HEF. apply concat_empty_r.
      rewrite <- HEF.
      apply typing_weakening; rewrite concat_empty_r; eauto.
    + binds_cases H; apply* typing_var.
  - apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  - apply_fresh* typing_tabs as Y.
    rewrite* subst_ee_open_te_var.
    rewrite* subst_ee_open_te_var.
    apply_ih_bind* H1.
  - apply_fresh* typing_let as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H1.
Qed.

(* Lemma okt_from_wft : forall Σ E T,  (may not be provable?) *)
(*     wft Σ E T -> okt Σ E. *)
(*   introv W. *)
(*   inversions W. *)

Lemma typing_through_subst_te : forall Σ E F Z e T P,
    {Σ, E & (withtyp Z) & F} ⊢ e ∈ T ->
    wft Σ E P ->
    {Σ, E & map (subst_tb Z P) F} ⊢ (subst_te Z P e) ∈ (subst_tt Z P T).
Proof.
  introv Typ W.
  inductions Typ; introv; simpls subst_tt; simpls subst_te; eauto.
  - apply* typing_var. rewrite* (@map_subst_tb_id Σ E Z P).
    binds_cases H; unsimpl_map_bind*.
    apply* okt_subst_tb.
  - apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_var V)).
    rewrite* subst_te_open_ee_var.
    apply_ih_map_bind* H0.
    apply* wft_subst_tb.
    admit.
  - apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P bind_typ).
    rewrite* subst_te_open_te_var. admit. admit.
    rewrite* subst_tt_open_tt_var. admit. admit.
  - apply* typing_tapp; admit.
  - admit.
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
    expand_env_empty E.
    apply* typing_through_subst_ee.
    fold_env_empty.
  - inversions Htyp.
    pick_fresh X. forwards~ K: (H9 X).
    rewrite* (@subst_te_intro X).
    rewrite* (@subst_tt_intro X).
    expand_env_empty E.
    erewrite <- map_empty.
    apply* typing_through_subst_te.
    fold_env_empty.
  - inversion Htyp; subst; eauto.
  - inversion Htyp; subst; eauto.
  - (* let *)
    pick_fresh x. forwards~ K: (H0 x).
    rewrite* (@subst_ee_intro x).
    expand_env_empty E.
    apply* typing_through_subst_ee.
    fold_env_empty.
Qed.
