Set Implicit Arguments.
Require Import Prelude.
Require Import Infrastructure.
Require Import Regularity.
Require Import TLC.LibLN.

Lemma term_through_subst : forall e x u,
    term u ->
    term e ->
    term (subst_ee x u e).
  introv Htermu Hterme.
  induction e; eauto;
    try solve [
          cbn; case_if; eauto
        | cbn; eauto
        | inversion Hterme; subst; cbn; econstructor; eauto
        ].
Qed.

#[export] Hint Resolve okt_is_ok.

(* Lemma okt_subst_tb : forall Σ Z P E F, *)
(*     okt Σ (E & (withtyp Z) & F) -> *)
(*     wft Σ E P -> *)
(*     okt Σ (E & map (subst_tb Z P) F). *)
(* Proof. *)
(*   introv O W. induction F using env_ind. *)
(*   - rewrite map_empty. rewrite concat_empty_r in *. *)
(*     lets*: (okt_push_typ_inv O). *)
(*   - rewrite map_push. rewrite concat_assoc in *. *)
(*     lets HPI: okt_push_inv O; destruct HPI as [? | Hex_bind]; subst. *)
(*     + lets (?&?): (okt_push_typ_inv O). *)
(*       applys~ okt_sub. *)
(*     + inversions Hex_bind. *)
(*       lets (?&?&?): (okt_push_var_inv O). *)
(*       applys~ okt_typ. applys* wft_subst_tb. *)
(* Qed. *)

Lemma okt_strengthen_simple : forall Σ D E F,
    okt Σ D (E & F) -> okt Σ D E.
  introv O.
  induction F using env_ind.
  - fold_env_empty_H.
  - rewrite concat_assoc in O.
    apply IHF.
    inversion O.
    + false* empty_push_inv.
    + lets [? [? ?]]: eq_push_inv H; subst. auto.
Qed.

#[export] Hint Resolve okt_strengthen_simple.

(** ** Environment is unchanged by substitution from a fresh name *)


(* Lemma map_subst_tb_id : forall Σ G Z P, *)
(*     okt Σ D G -> Z # G -> G = map (subst_tb Z P) G. *)
(* Proof. *)
(*   induction 1; intros Fr; autorewrite with rew_env_map; simpl. *)
(*   - auto. *)
(*   - rewrite* <- IHokt. *)
(*   - rewrite* <- IHokt. *)
(*     rewrite* subst_tt_fresh. *)
(*     apply* notin_fv_wf. *)
(* Qed. *)

(* Hint Resolve map_subst_tb_id. *)

Ltac renameIHs H Heq :=
  match goal with
  | IH: forall X, X \notin ?L -> typing _ _ _ _ |- _ =>
    rename IH into H end;
  match goal with
  | IH: forall X, X \notin ?L -> forall E0 G0, ?P1 -> ?P2 |- _ =>
    rename IH into Heq end.

Lemma wft_weaken_simple : forall Σ D1 D2 E,
    wft Σ D1 E ->
    wft Σ (D1 |,| D2) E.
  intros.
  rewrite <- (List.app_nil_r (D1 |,| D2)).
  apply wft_weaken.
  clean_empty_Δ. auto.
Qed.

Lemma okt_weakening_delta : forall Σ D1 D2 E X,
    okt Σ (D1 |,| D2) E ->
    X # E ->
    X \notin domΔ D1 ->
    X \notin domΔ D2 ->
    okt Σ (D1 |,| [tc_var X] |,| D2) E.
  introv Hokt FE FD1 FD2; gen_eq D': (D1 |,| D2). gen D2.
  induction Hokt; econstructor; subst; auto using wft_weaken.
  apply notin_domΔ_eq.
  rewrite notin_domΔ_eq in H1. destruct H1.
  split; auto.
  apply notin_domΔ_eq; split; auto.
  cbn.
  rewrite notin_union; split; auto.
  apply notin_inverse.
  rewrite dom_concat in FE. rewrite dom_single in FE. auto.
Qed.

Ltac fresh_intros :=
    let envvars := gather_vars in
    intros;
    repeat match goal with
           (* TODO find only uninstantiated *)
      | [ H: ?x \notin ?L |- _ ] =>
        instantiate (1:=envvars) in H
           end.

Lemma typing_weakening_delta:
  forall (u : trm) (Σ : GADTEnv) (D1 D2 : list typctx_elem) (E : env bind) (U : typ) (Y : var),
    {Σ, D1 |,| D2, E} ⊢ u ∈ U ->
    Y # E ->
    Y \notin domΔ D1 ->
    Y \notin domΔ D2 ->
    {Σ, D1 |,| [tc_var Y] |,| D2, E} ⊢ u ∈ U.
Proof.
  introv Typ FE FD1 FD2; gen_eq D': (D1 |,| D2); gen D2.
  induction Typ; introv EQ FD2; subst;
    try solve [
          econstructor; fresh_intros; eauto
        | econstructor; eauto using okt_weakening_delta; eauto using wft_weaken
        ].
  - econstructor; auto;
    try let envvars := gather_vars in
    instantiate (1:=envvars); auto.
    intros.
    lets* IH: H1 X (D2 |,| [tc_var X]).
    repeat rewrite <- List.app_assoc in *.
    apply IH; auto.
    rewrite notin_domΔ_eq. split; auto.
    cbn. rewrite notin_union.
    split; auto.
  - econstructor; eauto.
    try let envvars := gather_vars in
    introv Hin Hlen Hdist Afresh xfreshL xfreshA;
    instantiate (1:=envvars) in xfreshL.
    lets IH: H4 Hin Hlen (D2 |,| tc_vars Alphas); eauto.
    + introv Ain. lets*: Afresh Ain.
    + eauto.
    + repeat rewrite List.app_assoc in *.
      apply IH; auto.
      rewrite notin_domΔ_eq; split; auto.
      apply notin_dom_tc_vars.
      intro HF.
      lets HF2: from_list_spec HF.
      lets HF3: LibList_mem HF2.
      lets HF4: Afresh HF3.
      eapply notin_same.
      instantiate (1:=Y).
      eauto.
Qed.

Lemma typing_weakening_delta_many : forall Σ Δ E As u U,
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A \notin domΔ Δ) ->
    DistinctList As ->
    {Σ, Δ, E} ⊢ u ∈ U ->
    {Σ, Δ |,| tc_vars As, E} ⊢ u ∈ U.
  induction As as [| Ah Ats]; introv AE AD Adist Typ.
  - cbn. clean_empty_Δ. auto.
  - cbn. fold_delta.
    inversions Adist.
    rewrite List.app_assoc.
    apply typing_weakening_delta; auto with listin.
    apply notin_dom_tc_vars.
    intro HF.
    apply from_list_spec in HF.
    apply LibList_mem in HF.
    auto.
Qed.

Lemma okt_weakening_delta_many : forall Σ D1 D2 As E,
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A \notin domΔ D1) ->
    (forall A, List.In A As -> A \notin domΔ D2) ->
    DistinctList As ->
    okt Σ (D1 |,| D2) E ->
    okt Σ (D1 |,| tc_vars As |,| D2) E.
  induction As as [| Ah Ats]; introv AE AD1 AD2 Adist Hok.
  - cbn. clean_empty_Δ. auto.
  - cbn. fold_delta.
    inversions Adist.
    rewrite List.app_assoc.
    rewrite <- (List.app_assoc (D1 |,| [tc_var Ah]) (tc_vars Ats)).
    apply okt_weakening_delta; auto with listin.
    + rewrite List.app_assoc.
      apply IHAts; auto with listin.
    + apply notin_domΔ_eq. split; auto with listin.
      apply notin_dom_tc_vars.
      intro HF.
      apply from_list_spec in HF.
      apply LibList_mem in HF.
      auto.
Qed.

Lemma typing_weakening : forall Σ Δ E F G e T,
    {Σ, Δ, E & G} ⊢ e ∈ T ->
    okt Σ Δ (E & F & G) ->
    {Σ, Δ, E & F & G} ⊢ e ∈ T.
Proof.
  introv HTyp. gen F.
  inductions HTyp; introv Ok; eauto.
  - apply* typing_var. apply* binds_weaken.
  - econstructor; eauto.
    let env := gather_vars in
    instantiate (1:=env).
    introv xfresh.
    lets IH: H0 x E (G & x ~: V); auto.
    rewrite <- concat_assoc.
    apply IH.
    + apply JMeq_from_eq. auto using concat_assoc.
    + rewrite concat_assoc.
      econstructor; eauto.
      assert (xL: x \notin L); auto.
      lets Typ: H xL.
      lets [? [? ?]]: typing_regular Typ.
      eapply okt_is_wft. eauto.
  - apply_fresh* typing_tabs as X.
    lets IH: H1 X E G; auto.
    apply IH.
    + auto using JMeq_from_eq.
    + rewrite <- (List.app_nil_r (Δ |,| [tc_var X])).
      apply okt_weakening_delta; clean_empty_Δ; cbn; auto.
  - apply_fresh* typing_fix as x.
    lets IH: H1 x E (G & x ~: T); auto.
    rewrite <- concat_assoc.
    apply IH; repeat rewrite concat_assoc; auto.
    constructor; auto.
    lets [? [? ?]]: typing_regular T; eauto.
  - apply_fresh* typing_let as x.
    lets IH: H0 x E (G & x ~: V); auto.
    rewrite <- concat_assoc.
    apply IH; repeat rewrite concat_assoc; auto.
    constructor; auto.
    lets [? [? ?]]: typing_regular V; eauto.
  - eapply typing_case; eauto.
    let envvars := gather_vars in
    (introv Inzip AlphasArity ADistinct Afresh xfresh xfreshA;
     instantiate (1:=envvars) in Afresh).
    assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
      [ introv Ain; lets*: Afresh Ain | idtac ].
    assert (xfreshL: x \notin L); eauto.
    lets* IH1: H3 Inzip Alphas x AlphasArity ADistinct.
    lets* IH2: IH1 AfreshL xfreshL xfreshA.
    lets IHeq1: H4 Inzip Alphas x AlphasArity ADistinct.
    lets* IHeq2: IHeq1 AfreshL xfreshL xfreshA.

    lets IHeq3: IHeq2 E (G & x ~ bind_var (open_tt_many_var Alphas (Cargtype def))) F.
    + apply JMeq_from_eq.
      rewrite concat_assoc. trivial.
    + rewrite concat_assoc in IHeq3.
      apply IHeq3.
      constructor; auto.
      * rewrite <- (List.app_nil_r (Δ |,| tc_vars Alphas)).
        apply okt_weakening_delta_many; clean_empty_Δ;
        try solve [introv Ain; cbn; lets: Afresh Ain; auto]; auto.
      * lets [Hokt [? ?]]: typing_regular IH2.
        inversions Hokt.
        -- false* empty_push_inv.
        -- lets [? [Heq ?]]: eq_push_inv H6; subst.
           inversions Heq; auto.
      * apply notin_domΔ_eq. split; auto.
        apply notin_dom_tc_vars. auto.
Qed.

(* Hint Resolve typing_implies_term wft_strengthen okt_strengthen. *)

Lemma typing_through_subst_ee : forall Σ Δ E F x u U e T,
    {Σ, Δ, E & (x ~: U) & F} ⊢ e ∈ T ->
    {Σ, Δ, E} ⊢ u ∈ U ->
    {Σ, Δ, E & F} ⊢ subst_ee x u e ∈ T.
  Ltac apply_ih :=
    match goal with
    | H: forall X, X \notin ?L -> forall E0 F0 x0 U0, ?P1 -> ?P2 |- _ =>
      apply_ih_bind* H end.
  introv TypT TypU.
  inductions TypT; introv; cbn; eauto using okt_strengthen;
    lets [okU [termU wftU]]: typing_regular TypU.
  - match goal with
    | [ H: okt ?A ?B ?C |- _ ] =>
      lets: okt_strengthen H
    end.
    case_var.
    + binds_get H. eauto.
      assert (E & F & empty = E & F) as HEF. apply concat_empty_r.
      rewrite <- HEF.
      apply typing_weakening; rewrite concat_empty_r; eauto.
    + binds_cases H; apply* typing_var.
  - apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - apply_fresh* typing_tabs as Y; rewrite* subst_ee_open_te_var.
    match goal with
    | [ H: forall X, X \notin ?L -> forall E0 F0 x0 U0, ?P1 -> ?P2 |- _ ] =>
      apply* H
    end.
    rewrite <- (List.app_nil_r (Δ |,| [tc_var Y])).
    apply typing_weakening_delta; clean_empty_Δ; cbn; auto.
  - apply_fresh* typing_fix as y; rewrite* subst_ee_open_ee_var.
    apply_ih.
  - apply_fresh* typing_let as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - econstructor; eauto.
    + unfold map_clause_trm_trm.
      rewrite* List.map_length.
    + introv inzip.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets*: H2 Hzip.
    + introv inzip.
      let env := gather_vars in
      intros Alphas xClause Alen Adist Afresh xfresh xfreshA;
        instantiate (1:=env) in xfresh.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets* IH: H4 Hzip.

      assert (Htypfin: {Σ, Δ |,| tc_vars Alphas , E & F & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))}
                ⊢ subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause) ∈ Tc).
      * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
          [ introv Ain; lets*: Afresh Ain | idtac ].
        assert (xfreshL: xClause \notin L); eauto.
        lets Htmp: IH Alphas xClause Alen Adist AfreshL.
        lets Htmp2: Htmp xfreshL xfreshA.
        lets Htmp3: Htmp2 E (F & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))) x U.
        cbn in Htmp3.
        rewrite <- concat_assoc.
        apply* Htmp3.
        apply JMeq_from_eq.
        eauto using concat_assoc.
        apply typing_weakening_delta_many; auto;
          try introv Ain; lets: Afresh Ain; auto.
      * assert (Horder:
                  subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause)
                  =
                  open_te_many_var Alphas (subst_ee x u clT') open_ee_var xClause).
        -- rewrite* <- subst_ee_open_ee_var.
           f_equal.
           apply* subst_commutes_with_unrelated_opens_te_ee.
        -- rewrite* <- Horder.
Qed.

(* Lemma okt_strengthen_2 : forall Σ E Z P F, *)
(*     wft Σ E P -> *)
(*     okt Σ (E & (withtyp Z) & F) -> *)
(*     okt Σ (E & (EnvOps.map (subst_tb Z P) F)). *)
(*   introv WP O. induction F using env_ind. *)
(*   - rewrite concat_empty_r in *. lets*: (okt_push_typ_inv O). *)
(*     rewrite map_empty. *)
(*     rew_env_concat. eauto. *)
(*   - rewrite concat_assoc in *. *)
(*     lets Hinv: okt_push_inv O; inversions Hinv. *)
(*     + lets (?&?): (okt_push_typ_inv O). *)
(*       rewrite map_concat. *)
(*       rewrite map_single. *)
(*       rewrite concat_assoc. *)
(*       applys~ okt_sub. *)
(*     + match goal with *)
(*       | H: exists T, v = bind_var T |- _ => *)
(*         rename H into Hexists_bindvar end. *)
(*       inversions Hexists_bindvar. *)
(*       lets (?&?&?): (okt_push_var_inv O). *)
(*       rewrite map_concat. *)
(*       rewrite map_single. *)
(*       rewrite concat_assoc. *)
(*       applys~ okt_typ. *)
(*       applys* wft_subst_tb. *)
(* Qed. *)

Lemma okt_strengthen_simple_delta : forall Σ Δ E Z,
    okt Σ (Δ |,| [tc_var Z]) E ->
    Z # E ->
    Z \notin fv_env E ->
    okt Σ Δ E.
  intros.
  rewrite <- (List.app_nil_r Δ).
  eapply okt_strengthen_delta_var with Z; auto.
  clean_empty_Δ. auto.
Qed.

(* TODO move and merge with _1 *)
Lemma wft_subst_tb_2 : forall Σ D1 D2 Z P T,
  wft Σ (D1 |,| [tc_var Z] |,| D2) T ->
  wft Σ (D1 |,| D2) P ->
  wft Σ (D1 |,| D2) (subst_tt Z P T).
Proof.
  introv WT WP; gen_eq G: (D1 |,| [tc_var Z] |,| D2). gen D2.
  induction WT; intros; subst; simpl subst_tt; auto.
  - case_var*.
    constructor.
    unfold is_var_defined in *.
    repeat destruct_app_list; auto using List.in_or_app.
    cbn in H. destruct H.
    * congruence.
    * contradiction.
  - apply_fresh* wft_all as Y.
    lets: wft_type.
    rewrite* subst_tt_open_tt_var.
    lets* IH: H0 Y (D2 |,| [tc_var Y]).
    rewrite <- List.app_assoc.
    apply IH; auto using List.app_assoc.
    rewrite List.app_assoc.
    apply* wft_weaken_simple.
  - apply* wft_gadt.
    + introv Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [U [? Tin]]; subst.
      apply* H0.
    + apply List.map_length.
Qed.

Lemma okt_strengthen_delta_var_subst : forall Σ D1 D2 E X P,
    wft Σ (D1 |,| D2) P ->
    okt Σ (D1 |,| [tc_var X] |,| D2) E ->
    X # E ->
    okt Σ (D1 |,| D2) (map (subst_tb X P) E).
  introv WFT OKT.
  gen_eq G: (D1 |,| [tc_var X] |,| D2). gen D2 X.
  induction OKT; introv WFT Heq XE; subst.
  - rewrite map_empty.
    econstructor; auto.
  - rewrite map_concat.
    rewrite map_single.
    constructor; auto.
    + apply* wft_subst_tb_2.
    + repeat (apply notin_domΔ_eq in H1; destruct H1).
      apply notin_domΔ_eq; split*.
Qed.

Lemma typing_through_subst_te:
  forall Σ Δ1 Δ2 E Z e P T,
    {Σ, Δ1 |,| [tc_var Z] |,| Δ2, E} ⊢ e ∈ T ->
    wft Σ (Δ1 |,| Δ2) P ->
    Z \notin fv_typ P ->
    Z # E ->
    {Σ, Δ1 |,| Δ2, map (subst_tb Z P) E} ⊢ subst_te Z P e ∈ subst_tt Z P T.
Proof.
  introv Typ. gen_eq G: (Δ1 |,| [tc_var Z] |,| Δ2). gen Δ2.
  induction Typ; introv GEQ Hwft FPZ FPE; subst;
    try match goal with
        | [ H: okt Σ (Δ1 |,| [tc_var Z] |,| ?Δ2) E |- _ ] =>
            lets Hokt2: okt_strengthen_delta_var_subst P H
    end;
    cbn; auto;
      try solve [econstructor; lets*: IHTyp Hwft FPE].
  - econstructor; auto.
    fold (subst_tb Z P (bind_var T)).
    apply* binds_map.
  - assert (Hokconstr: okConstructorDef Σ Tarity (mkGADTconstructor (length Ts) CargType CretTypes)).
    + apply* gadt_constructor_ok. apply* okt_implies_okgadt.
      lets*: typing_regular Typ.
    + inversion Hokconstr
        as [? ? ? ? ? Harity Warg Wret Farg Fret]; subst.
      econstructor; eauto.
      * apply* List.map_length.
      * apply* subst_commutes_open_tt_many.
        rewrite Farg. eauto.
      * introv Timaped.
        lets* Hinmap: List.in_map_iff (subst_tt Z P) Ts T.
        apply Hinmap in Timaped.
        destruct Timaped as [T' [Teq T'in]].
        subst.
        apply* wft_subst_tb_2.
      * apply* subst_commutes_open_tt_many.
        cbn. rewrite* fold_empty.
  - apply_fresh* typing_abs as x.
    rewrite subst_te_open_ee_var.
    fold (subst_tb Z P (bind_var V)).
    rewrite <- map_single.
    rewrite <- map_concat.
    apply H0; auto.
  - econstructor.
    + apply IHTyp1; auto.
    + apply IHTyp2; auto.
  - apply_fresh* typing_tabs as X.
    + rewrite* subst_te_open_te_var.
    + lets IH: H1 X (Δ2 |,| [tc_var X]); auto.
      rewrite <- List.app_assoc.
      rewrite* subst_tt_open_tt_var.
      rewrite* subst_te_open_te_var.
      apply IH; try rewrite List.app_assoc; trivial.
      * apply* wft_weaken_simple.
  - rewrite* subst_tt_open_tt. apply* typing_tapp.
    apply* wft_subst_tb_2.
  - apply_fresh* typing_fix as y.
    rewrite* subst_te_open_ee_var.
    unsimpl (subst_tb Z P (bind_var T)).
    rewrite* subst_te_open_ee_var.
    rewrite <- map_single.
    rewrite <- map_concat.
    apply* H1.
  - apply_fresh* typing_let as y.
    unsimpl (subst_tb Z P (bind_var V)).
    rewrite* subst_te_open_ee_var.
    rewrite <- map_single.
    rewrite <- map_concat.
    apply* H0.
  - apply_fresh* typing_case as x.
    + unfold map_clause_trm_trm.
      rewrite* List.map_length.
    + introv inzip.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets*: H2 Hzip.
    + introv inzip.
      intros Alphas xClause Alen Adist Afresh xfresh xfreshA.

      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.

      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets* IH: H4 Hzip.
      cbn in IH.

      assert (Htypfin: {Σ, Δ1 |,| Δ2 |,| tc_vars Alphas,
                        map (subst_tb Z P) E &
                           xClause ~ bind_var (subst_tt Z P (open_tt_many_var Alphas (Cargtype def)))}
                         ⊢ subst_te Z P (open_te_many_var Alphas clT' open_ee_var xClause)
                         ∈ subst_tt Z P Tc).
      * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
          [ introv Ain; lets*: Afresh Ain | idtac ].
        assert (xfreshL: xClause \notin L); eauto.
        lets Htmp: IH Alphas xClause Alen Adist AfreshL.
        lets Htmp2: Htmp xfreshL xfreshA.
        lets Htmp3: Htmp2 (Δ2 |,| tc_vars Alphas).
        autorewrite with rew_env_map in Htmp3.
        cbn in Htmp3.
        rewrite <- List.app_assoc.
        apply Htmp3; try rewrite List.app_assoc; auto.
        apply* wft_weaken_simple.
      * rewrite (@subst_tt_fresh _ _ (open_tt_many_var Alphas (Cargtype def))) in Htypfin.
        2: {
          lets [Hokt ?]: typing_regular Typ.
          lets okgadt: okt_implies_okgadt Hokt.
          unfold okGadt in okgadt.
          destruct okgadt as [okΣ okCtors].
          lets [defsNe okDefs]: okCtors H0.
          lets indef: fst_from_zip Hzip.
          lets okCtor: okDefs indef.
          inversions okCtor.
          cbn.
          lets Hsub: fv_smaller_many Alphas argT.
          lets snsu: split_notin_subset_union Z Hsub.
          apply snsu.
          - rewrite H8. eauto.
          - intro Zin.
            lets [A [Ain Aeq]]: in_from_list Zin.
            subst.
            lets: Afresh Ain.
            assert (Hfalse: A \notin \{A}); eauto.
            apply Hfalse.
            apply in_singleton_self.
        }
        assert (Horder:
                  open_te_many_var Alphas (subst_te Z P clT') open_ee_var xClause
                  =
                  subst_te Z P (open_te_many_var Alphas clT' open_ee_var xClause)).
        1: {
          rewrite* <- subst_commutes_with_unrelated_opens_te_te.
          - rewrite* subst_te_open_ee_var.
          - intros A Ain.
            intro. subst.
            lets: Afresh Ain.
            assert (HF: Z \notin \{Z}); eauto.
            apply HF. apply in_singleton_self.
        }
        rewrite* Horder.
Qed.

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

Lemma typing_through_subst_te_2 :
  forall Σ Δ1 Δ2 E Z e P T,
    {Σ, Δ1 |,| [tc_var Z] |,| Δ2, E} ⊢ e ∈ T ->
    wft Σ (Δ1 |,| Δ2) P ->
    Z \notin fv_typ P ->
    Z # E ->
    Z \notin fv_env E ->
    {Σ, Δ1 |,| Δ2, E} ⊢ subst_te Z P e ∈ subst_tt Z P T.
  intros.
  rewrite <- (@subst_tb_id_on_fresh E Z P); auto with listin.
  apply* typing_through_subst_te.
Qed.

Lemma typing_through_subst_te_many : forall As Σ Δ E F e T Ps,
    {Σ, (Δ |,| tc_vars As), E & F} ⊢ e ∈ T ->
    length As = length Ps ->
    (forall P, List.In P Ps -> wft Σ Δ P) ->
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A # F) ->
    (forall A P, List.In A As -> List.In P Ps -> A \notin fv_typ P) ->
    (forall A, List.In A As -> A \notin fv_env E) ->
    DistinctList As ->
    {Σ, Δ, E & map (subst_tb_many As Ps) F} ⊢ (subst_te_many As Ps e) ∈  subst_tt_many As Ps T.
  induction As as [| Ah Ats]; introv Htyp Hlen Pwft AE AF AP AEE Adist;
    destruct Ps as [| Ph Pts]; try solve [cbn in *; congruence].
  - cbn in *. clean_empty_Δ.
    rewrite map_def.
    rewrite <- LibList_map.
    rewrite <- map_id; auto.
    intros. destruct x as [? [?]].
    cbv. auto.
  - cbn.
    inversions Adist.
    lets IH0: IHAts Σ (Δ) (map (subst_tb Ah Ph) E) (map (subst_tb Ah Ph) F)
                   (subst_te Ah Ph e).
    lets IH: IH0 (subst_tt Ah Ph T) Pts.
    rewrite <- (@subst_tb_id_on_fresh E Ah Ph).
    rewrite subst_tb_many_split.
    apply IH; auto with listin.
    + lets: typing_through_subst_te Σ Δ (tc_vars Ats) Ah.
      rewrite <- map_concat.
      apply H; auto with listin.
      * rewrite <- List.app_assoc.
        cbn.
        unfold tc_vars.
        rewrite <- List.map_cons.
        fold (tc_vars (Ah :: Ats)).
        auto.
      * rewrite <- (List.app_nil_r (Δ ++ tc_vars Ats)).
        apply wft_weaken.
        clean_empty_Δ. auto with listin.
    + lets: fv_env_subst.
      auto with listin.
    + auto with listin.
Qed.

Theorem preservation_thm : preservation.
  Ltac find_hopen :=
    let Hopen := fresh "Hopen" in
    match goal with
    | H: forall x, x \notin ?L -> typing _ _ _ _ _ |- _ =>
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
    introv Hred; inversions Hred;
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
    rewrite <- (List.app_nil_r Δ).
    apply* typing_through_subst_te_2; clean_empty_Δ; auto.
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
  - (* matchgadt *)

    (* we reduce to one of the branches which correspond to their definitions in type *)
    lets* [Def [nthDef Inzip]]: nth_error_implies_zip_swap Defs H10.
    lets HclTyp: H3 Inzip.
    remember (Cargtype Def) as argT.

    (* prepare fresh vars *)
    let fresh := gather_vars in
    lets* [Alphas [Hlen [Adist Afresh]]]: exist_alphas fresh (length Ts0).
    pick_fresh x.

    match goal with
    | [ H: term (trm_constructor ?A ?B ?C) |- _ ] =>
      inversions H7
    end.

    (* extract info from well-formedness of GADT env Σ - our constructors are well formed *)
    lets [Hokt ?]: typing_regular Htyp.
    lets okgadt: okt_implies_okgadt Hokt.
    unfold okGadt in okgadt.
    destruct okgadt as [okΣ okCtors].
    lets [defsNe okDefs]: okCtors H0.
    lets indef: fst_from_zip Inzip.
    lets okCtor: okDefs indef.
    inversion okCtor.
    clear H15 H16 Tarity0 Σ0.
    rename Carity into DefArity.

    (* replace open with subst+open_var *)
    rewrite (@subst_ee_intro x); trivial;
      [ idtac
      | apply fv_open_te_many;
        [ introv Tin;
          apply* fv_typs_notin
        | auto ]
      ].

    rewrite (@subst_te_intro_many Alphas _ Ts0); auto;
      [ idtac
      | introv Ain; subst; cbn; cbn in Afresh; lets*: Afresh Ain
      | introv Ain Tin; lets: Afresh Ain; apply* fv_typs_notin
      ].

    (* use fact that subst preserves typing *)
    expand_env_empty E.
    apply typing_through_subst_ee with (open_tt_many Ts0 (Cargtype Def)).
    (* apply typing_through_subst_ee with (open_tt_many_var Alphas (Cargtype Def)). *)
    2: {
      subst. cbn.
      inversions Htyp.
      lets Hbeq: binds_ext H19 H0.
      inversions Hbeq.
      rewrite nthDef in H20. inversions H20.
      trivial.
    }

    rewrite (@subst_tt_intro_many Alphas _ Ts0); auto;
      [ idtac
      | introv Ain; subst; cbn; cbn in Afresh; lets*: Afresh Ain
      | introv Ain Tin; lets: Afresh Ain; apply* fv_typs_notin
      ].

    (* instantiate the inductive hypothesis *)
    assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
      [ introv Ain; lets*: Afresh Ain | idtac].
    assert (xfreshL: x \notin L); auto.
    assert (xfreshA: x \notin from_list Alphas); auto.

    assert (length Alphas = Carity Def);
      [ lets Hclarity: H2 Inzip; rewrite <- Hclarity; cbn; trivial | idtac ].
    lets* IH: H3 Inzip Alphas x Adist xfreshA.
    cbn in IH.

    rewrite subst_te_many_commutes_open; auto;
      [ idtac
      | introv Ain; lets: Afresh Ain;
        lets: from_list_spec2 Ain;
        intro; subst; auto
      ].

    fold (subst_tb_many Alphas Ts0 (bind_var (open_tt_many_var Alphas (Cargtype Def)))).
    rewrite <- map_single.
    fold_env_empty.

    rewrite subst_tt_many_free with Alphas Ts0 Tc;
      [ idtac | introv Ain; lets*: Afresh Ain ].

    apply typing_through_subst_te_many; trivial.
    + inversions Htyp.
      intros; auto with listin.
    + intros A Ain.
      lets: Afresh Ain. auto.
    + autorewrite with rew_env_dom.
      intros A Ain.
      apply notin_inverse.
      intro HF.
      apply xfreshA.
      rewrite in_singleton in HF. subst.
      apply from_list_spec2. auto.
    + introv Ain Tin.
      apply fv_typs_notin with Ts0; auto.
      lets: Afresh Ain.
      auto with listin.
    + introv Ain; lets*: Afresh Ain.
Qed.

