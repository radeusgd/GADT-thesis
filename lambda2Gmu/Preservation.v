Set Implicit Arguments.
Require Import Definitions.
Require Import Infrastructure.
Require Import CanonicalForms.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

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

Lemma okt_subst_tb : forall Σ Z P E F,
  okt Σ (E & (withtyp Z) & F) ->
  wft Σ E P ->
  okt Σ (E & map (subst_tb Z P) F).
Proof.
  introv O W. induction F using env_ind.
  - rewrite map_empty. rewrite concat_empty_r in *.
    lets*: (okt_push_typ_inv O).
  - rewrite map_push. rewrite concat_assoc in *.
    lets HPI: okt_push_inv O; destruct HPI as [? | Hex_bind]; subst.
    + lets (?&?): (okt_push_typ_inv O).
      applys~ okt_sub.
    + inversions Hex_bind.
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
    inversion O as [| ? ? ? ? H1 H2 Heq | ? ? ? ? H1 H2 H3 H4 Heq]. subst.
    + exfalso; apply* empty_push_inv.
    + apply eq_push_inv in Heq. destructs Heq; subst. auto.
    + apply eq_push_inv in Heq. destructs Heq; subst. auto.
Qed.

Hint Resolve okt_strengthen_simple.

(** ** Environment is unchanged by substitution from a fresh name *)

Lemma in_fold_exists : forall TV TT P ls Z X,
    X \in List.fold_left (fun (fv : fset TV) (T : TT) => fv \u P T) ls Z ->
          (exists T, List.In T ls /\ X \in P T) \/ X \in Z.
  induction ls; introv Hin.
  - right.
    cbn in *. eauto.
  - cbn in Hin.
    lets* IH: IHls (Z \u P a) X Hin.
    destruct IH as [IH | IH].
    + destruct IH as [T [Tin PT]].
      left. exists T. eauto with listin.
    + rewrite in_union in IH.
      destruct IH as [IH | IH]; eauto with listin.
Qed.

Lemma notin_fv_tt_open : forall Y X T,
  X \notin fv_typ (T open_tt_var Y) ->
  X \notin fv_typ T.
Proof.
  unfold open_tt.
  introv FO.
  lets* characterized: fv_open T (typ_fvar Y) 0.
  destruct characterized as [Hc | Hc]; rewrite Hc in FO; eauto.
Qed.

Lemma notin_fv_wf : forall Σ E X T,
  wft Σ E T -> X # E -> X \notin fv_typ T.
Proof.
  induction 1 as [ | ? ? ? Hbinds | | | |];
    introv Fr; simpl; eauto.
  - rewrite notin_singleton. intro. subst. applys binds_fresh_inv Hbinds Fr.
  - notin_simpl; auto. pick_fresh Y. apply* (@notin_fv_tt_open Y).
  - intro Hin.
    lets* Hex: in_fold_exists Hin.
    destruct Hex as [Hex | Hex].
    + destruct Hex as [T [Tin fvT]].
      lets* Hf: H0 T Tin.
    + apply* in_empty_inv.
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

Ltac renameIHs H Heq :=
  match goal with
  | IH: forall X, X \notin ?L -> typing _ _ _ _ |- _ =>
    rename IH into H end;
  match goal with
  | IH: forall X, X \notin ?L -> forall E0 G0, ?P1 -> ?P2 |- _ =>
    rename IH into Heq end.

Lemma typing_weakening : forall Σ E F G e T,
   {Σ, E & G} ⊢ e ∈ T ->
   okt Σ (E & F & G) ->
   {Σ, E & F & G} ⊢ e ∈ T.
Proof.
  introv HTyp. gen F.
  inductions HTyp; introv Ok; eauto.
  - apply* typing_var. apply* binds_weaken.
  - admit.
  - renameIHs IH IHeq.
    apply_fresh* typing_abs as x.
    forwards~ K: (IH x).
    apply_ih_bind (IHeq x); eauto.
    econstructor; eauto.
    lets (Hokt&?&?): typing_regular K.
    lets (?&?&?): okt_push_var_inv Hokt.
    apply* wft_weaken.
  - renameIHs IH IHeq.
    apply_fresh* typing_tabs as X.
    forwards~ K: (IH X).
    apply_ih_bind (IHeq X); auto.
    econstructor; eauto.
  - apply* typing_tapp. apply* wft_weaken.
  - renameIHs IH IHeq.
    apply_fresh* typing_fix as x.
    forwards~ K: (IH x).
    apply_ih_bind (IHeq x); eauto.
    econstructor; eauto.
    lets (Hokt&?&?): typing_regular K.
    lets (?&?&?): okt_push_var_inv Hokt.
    apply* wft_weaken.
  - renameIHs IH IHeq.
    apply_fresh* typing_let as x.
    forwards~ K: (IH x).
    apply_ih_bind (IHeq x); eauto.
    econstructor; eauto.
    lets (Hokt&?&?): typing_regular K.
    lets (?&?&?): okt_push_var_inv Hokt.
    apply* wft_weaken.
Admitted.

Hint Resolve typing_implies_term wft_strengthen okt_strengthen.

Lemma typing_through_subst_ee : forall Σ E F x u U e T,
    {Σ, E & (x ~: U) & F} ⊢ e ∈ T ->
    {Σ, E} ⊢ u ∈ U ->
    {Σ, E & F} ⊢ subst_ee x u e ∈ T.

  (* H1 : forall X : var, *)
  (*      X \notin L -> *)
  (*      forall (E0 F0 : env bind) (x0 : var) (U0 : typ), *)
  (*      JMeq.JMeq (E & x ~ bind_var U & F & X ~ bind_typ) (E0 & x0 ~ bind_var U0 & F0) -> *)
  (*      {Σ, E0}⊢ u ∈ U0 -> *)
  (*      {Σ, E0 & F0}⊢ subst_ee x0 u (e1 open_te_var X) ∈ (T1 open_tt_var X) *)
  Ltac apply_ih :=
    match goal with
    | H: forall X, X \notin ?L -> forall E0 F0 x0 U0, ?P1 -> ?P2 |- _ =>
      apply_ih_bind* H end.
  introv TypT TypU.
  inductions TypT; introv; cbn; eauto.
  - assert (okt Σ (E & F)).
    + apply* okt_strengthen.
    + case_var.
      * binds_get H. eauto.
        assert (E & F & empty = E & F) as HEF. apply concat_empty_r.
        rewrite <- HEF.
        apply typing_weakening; rewrite concat_empty_r; eauto.
      * binds_cases H; apply* typing_var.
  - apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - apply_fresh* typing_tabs as Y; rewrite* subst_ee_open_te_var.
    apply_ih.
  - apply_fresh* typing_fix as y; rewrite* subst_ee_open_ee_var.
    apply_ih.
  - apply_fresh* typing_let as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
Qed.

(* Lemma okt_from_wft : forall Σ E T,  (may not be provable?) *)
(*     wft Σ E T -> okt Σ E. *)
(*   introv W. *)
(*   inversions W. *)

Hint Resolve okt_subst_tb.

Lemma typing_through_subst_te : forall Σ E F Z e T P,
    {Σ, E & (withtyp Z) & F} ⊢ e ∈ T ->
    wft Σ E P ->
    {Σ, E & map (subst_tb Z P) F} ⊢ (subst_te Z P e) ∈ (subst_tt Z P T).
Proof.
  Ltac apply_ih2 :=
    match goal with
    | H: forall X, X \notin ?L -> forall E0 F0 Z0, ?P1 -> ?P2 |- _ =>
      apply_ih_map_bind* H end.
  introv Typ W.
  inductions Typ; introv; simpls subst_tt; simpls subst_te; eauto.
  - apply* typing_var. rewrite* (@map_subst_tb_id Σ E Z P).
    match goal with
    | Hbinds: binds _ _ _ |- _ => binds_cases Hbinds; unsimpl_map_bind* end.
  - admit.
  - apply_fresh* typing_abs as y.
    unsimpl (subst_tb Z P (bind_var V)).
    rewrite* subst_te_open_ee_var.
    apply_ih2.
  - apply_fresh* typing_tabs as Y.
    + rewrite* subst_te_open_te_var.
    + unsimpl (subst_tb Z P bind_typ).
      rewrite* subst_tt_open_tt_var.
      rewrite* subst_te_open_te_var.
      apply_ih2.
  - rewrite* subst_tt_open_tt. apply* typing_tapp.
    apply* wft_subst_tb.
    apply* ok_concat_map.
    destructs (typing_regular Typ).
    match goal with
    | Hokt: okt _ _ |- _ =>
      lets*: okt_is_ok Hokt end.
  - apply_fresh* typing_fix as y.
    rewrite* subst_te_open_ee_var.
    unsimpl (subst_tb Z P (bind_var T)).
    rewrite* subst_te_open_ee_var.
    apply_ih2.
  - apply_fresh* typing_let as y.
    unsimpl (subst_tb Z P (bind_var V)).
    rewrite* subst_te_open_ee_var.
    apply_ih2.
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
  Ltac find_hopen :=
    let Hopen := fresh "Hopen" in
    match goal with
    | H: forall x, x \notin ?L -> typing _ _ _ _ |- _ =>
      rename H into Hopen
    end.
  Ltac find_hval :=
    let Hval := fresh "Hval" in
    match goal with
    | H: forall x, x \notin ?L -> value _ |- _ =>
      rename H into Hval
    end.
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
    pick_fresh x.
    find_hopen. forwards~ K: (Hopen x).
    rewrite* (@subst_ee_intro x).
    expand_env_empty E.
    apply* typing_through_subst_ee.
    fold_env_empty.
  - inversions Htyp.
    pick_fresh X.
    find_hopen. forwards~ K: (Hopen X).
    rewrite* (@subst_te_intro X).
    rewrite* (@subst_tt_intro X).
    expand_env_empty E.
    erewrite <- map_empty.
    apply* typing_through_subst_te.
    fold_env_empty.
  - inversion Htyp; subst; eauto.
  - inversion Htyp; subst; eauto.
  - (* fix *)
    pick_fresh x.
    find_hval.
    forwards~ K: (Hval x).
    rewrite* (@subst_ee_intro x).
    expand_env_empty E.
    apply* typing_through_subst_ee.
    fold_env_empty.
  - (* let *)
    pick_fresh x.
    find_hopen.
    forwards~ K: (Hopen x).
    rewrite* (@subst_ee_intro x).
    expand_env_empty E.
    apply* typing_through_subst_ee.
    fold_env_empty.
Qed.
