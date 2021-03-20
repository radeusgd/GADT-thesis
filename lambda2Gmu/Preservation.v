Set Implicit Arguments.
Require Import Prelude.
Require Import Infrastructure.
Require Import Regularity.
Require Import Equations.
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
  rewrite <- (List.app_nil_l (D1 |,| D2)).
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

Lemma okt_weakening_delta_eq : forall Σ D1 D2 E eq,
    okt Σ (D1 |,| D2) E ->
    okt Σ (D1 |,| [tc_eq eq] |,| D2) E.
  introv Hokt; gen_eq D': (D1 |,| D2). gen D2.
  induction Hokt; econstructor; subst; auto using wft_weaken.
  repeat rewrite notin_domΔ_eq in *. destruct H1.
  destruct eq; cbn.
  split~.
Qed.

Lemma subst_sources_from_match : forall Σ D Θ,
    subst_matches_typctx Σ D Θ ->
    substitution_sources Θ = domΔ D.
  induction 1; cbn; auto.
  fold (from_list (List.map fst Θ)).
  fold (substitution_sources Θ).
  rewrite~ IHsubst_matches_typctx.
Qed.

Lemma subst_match_remove_eq : forall Σ Θ D1 D2 T1 T2,
    subst_matches_typctx Σ (D1 |,| [tc_eq (T1 ≡ T2)] |,| D2) Θ ->
    subst_matches_typctx Σ (D1 |,| D2) Θ.
  introv Match.
  gen_eq D3: (D1 |,| [tc_eq (T1 ≡ T2)] |,| D2). gen D1 D2.
  induction Match; introv EQ; subst; eauto.
  - false List.app_cons_not_nil.
    cbn in EQ.
    eauto.
  - destruct D2; inversions EQ.
    constructor; try fold (D1 |,| D2); auto.
    fold_delta.
    repeat rewrite notin_domΔ_eq in *.
    destruct H1 as [[? ?] ?].
    split~.
  - destruct D2; inversions EQ.
    + cbn. auto.
    + constructor; auto.
Qed.

Lemma equation_weaken_eq:
  forall (Σ : GADTEnv) (D1 D2 : list typctx_elem) (T1 T2 U1 U2 : typ),
    entails_semantic Σ (D1 |,| D2) (T1 ≡ T2) ->
    entails_semantic Σ ((D1 |,| [tc_eq (U1 ≡ U2)]) |,| D2) (T1 ≡ T2).
Proof.
  introv H.
  cbn in *.
  introv M.
  apply H.
  apply subst_match_remove_eq with U1 U2. auto.
Qed.

Lemma subst_eq_strengthen : forall Θ T1 T2 Y T,
    Y \notin substitution_sources Θ ->
    (forall A U, List.In (A, U) Θ -> Y \notin fv_typ U) ->
    subst_tt' T1 Θ = subst_tt' T2 Θ ->
    subst_tt' (subst_tt Y T T1) Θ = subst_tt' (subst_tt Y T T2) Θ.
  induction Θ as [| [X U]]; introv FrSrc FrTrg EQ.
  - cbn in *.
    f_equal~.
  - cbn in *.
    fold_subst_src.
    assert (Y \notin fv_typ U).
    + eauto with listin.
    + rewrite~ subst_commute.
      rewrite (subst_commute U); auto.
      apply~ IHΘ.
      eauto with listin.
Qed.

Lemma subst_match_decompose_var : forall Σ D1 D2 Y Θ,
    subst_matches_typctx Σ ((D1 |,| [tc_var Y]) |,| D2) Θ ->
    exists Θ1 Θ2 U,
      Θ = Θ1 |,| [(Y, U)] |,| Θ2 /\
      subst_matches_typctx Σ D1 Θ1 /\
      substitution_sources Θ1 = domΔ D1 /\
      substitution_sources Θ2 = domΔ D2 /\
      Y \notin domΔ D1.
  induction D2; introv M; cbn in *.
  - inversions M.
    exists Θ0 (@List.nil (var * typ)) T.
    repeat split~.
    apply* subst_sources_from_match.
  - inversions M.
    + lets [O1 [O2 [U [EQ [M2 [S1 [S2 D]]]]]]]: IHD2 H2. subst.
      exists O1 ((A, T) :: O2) U.
      repeat split~.
      cbn. fold_subst_src.
      rewrite~ S2.
    + lets [O1 [O2 [U [EQ [M2 [S1 [S2 D]]]]]]]: IHD2 H1. subst.
      exists O1 O2 U.
      split~.
Qed.

Lemma subst_match_notin_srcs : forall Σ D O1 X U,
    subst_matches_typctx Σ D (O1 |, (X, U)) ->
    X \notin substitution_sources O1.
  introv M.
  gen_eq O0: (O1 |, (X, U)). gen O1.
  induction M; introv EQ; subst; auto.
  - inversion EQ.
  - inversions EQ. auto.
Qed.

Lemma subst_match_remove_right_var : forall Σ D1 X D2 O1 U O2 Y V,
    subst_matches_typctx Σ ((D1 |,| [tc_var X]) |,| D2) ((O1 |,| [(X, U)]) |,| (O2 |, (Y, V))) ->
    exists D3 D4,
      D2 = D3 |,| D4 /\
      subst_matches_typctx Σ ((D1 |,| [tc_var X]) |,| D3) ((O1 |,| [(X, U)]) |,| O2).
  induction D2 as [| [Z | [V1 V2]]]; introv M.
  - cbn in *.
    inversions M.
    false.
    apply H6.
    apply~ subst_match_notin_srcs2.
    apply List.in_or_app. cbn. eauto.
  - inversions M.
    exists D2 [tc_var Y].
    cbn.
    splits~.
  - inversions M.
    lets [D3 [D4 [EQ M2]]]: IHD2 H3.
    subst.
    exists D3 (D4 |, tc_eq (V1 ≡ V2)).
    cbn.
    splits~.
Qed.

Lemma subst_match_remove_right_var2 : forall Σ D1 X D2 O1 U,
    subst_matches_typctx Σ ((D1 |,| [tc_var X]) |,| D2) (O1 |, (X, U)) ->
    subst_matches_typctx Σ D1 O1.
  induction D2 as [| [Z | [V1 V2]]]; introv M.
  - cbn in *.
    inversions M.
    auto.
  - inversions M.
    fold_delta.
    repeat rewrite notin_domΔ_eq in *.
    destruct H7 as [[? HF]].
    cbn in HF.
    rewrite notin_union in HF.
    destruct HF as [HF ?].
    false* notin_same.
  - inversions M.
    lets~ IH: IHD2 H3.
Qed.

Lemma subst_eq_strengthen_gen : forall Θ1 Θ2 X U Σ D1 D2 T1 T2,
    subst_tt' T1 (Θ1 |,| Θ2) = subst_tt' T2 (Θ1 |,| Θ2) ->
    subst_matches_typctx Σ (D1 |,| [tc_var X] |,| D2) ((Θ1 |,| [(X, U)]) |,| Θ2) ->
    subst_tt' T1 ((Θ1 |,| [(X, U)]) |,| Θ2) = subst_tt' T2 ((Θ1 |,| [(X, U)]) |,| Θ2).
  induction Θ2 as [| [Y V]]; introv EQ M.
  - cbn in *.
    apply~ subst_eq_strengthen.
    + apply* subst_match_notin_srcs.
    + apply* subst_has_no_fv2.
      fold_delta.
      lets*: subst_match_remove_right_var2 M.
  - cbn.
    lets [D3 [D4 [EQ2 M2]]]: subst_match_remove_right_var M.
    apply* IHΘ2.
Qed.

Lemma subst_eq_weaken : forall Θ1 Θ2 T1 T2 X U,
    subst_tt' T1 ((Θ1 |,| [(X, U)]) |,| Θ2) = subst_tt' T2 ((Θ1 |,| [(X, U)]) |,| Θ2) ->
    X \notin fv_typ T1 \u fv_typ T2 ->
    (forall A U, List.In (A, U) Θ2 -> fv_typ U = \{}) ->
    subst_tt' T1 (Θ1 |,| Θ2) = subst_tt' T2 (Θ1 |,| Θ2).
  induction Θ2; introv EQ Fr Fr2.
  - cbn in *.
    repeat rewrite~ subst_tt_fresh in EQ.
  - destruct a as [Y P]; cbn in *.
    rewrite notin_union in *. destruct Fr.
    assert (X \notin fv_typ P).
    + rewrite Fr2 with Y P; auto.
    + apply IHΘ2 with X U; auto.
      * rewrite notin_union in *.
        split; apply~ fv_subst_tt.
      * introv Ain. eauto with listin.
Qed.

Lemma subst_match_remove_unused_var : forall Σ Θ1 Θ2 D1 D2 X T,
    subst_matches_typctx Σ (D1 |,| [tc_var X] |,| D2) (Θ1 |,| [(X, T)] |,| Θ2) ->
    X \notin fv_delta D2 ->
    subst_matches_typctx Σ (D1 |,| D2) (Θ1 |,| Θ2).
  introv Match.
  gen_eq D3: (D1 |,| [tc_var X] |,| D2). gen D1 D2.
  gen_eq Θ3: (Θ1 |,| [(X, T)] |,| Θ2). gen Θ1 Θ2.
  induction Match; introv EQ EQ2 Fr; subst; eauto.
  - false List.app_cons_not_nil.
    cbn in *.
    eauto.
  - destruct D2; inversions EQ;
      cbn in *;
      inversions EQ2.
    + destruct Θ2; inversions H3; auto.
      false H0.
      apply~ substitution_sources_from_in.
      apply List.in_or_app. cbn. auto.
    + destruct Θ2; inversions H3.
      * repeat rewrite notin_domΔ_eq in *.
        cbn in H1.
        rewrite notin_union in H1.
        destruct H1 as [[HF]].
        false HF. apply in_singleton_self.
      * constructor; try fold (Θ1 |,| Θ2); auto.
        -- fold (Θ1 |,| [(X, T)]) in *.
           repeat rewrite subst_src_app in *.
           repeat rewrite notin_union in *.
           destruct H0 as [[?]].
           split~.
        -- rewrite notin_domΔ_eq in *.
           destruct H1. cbn in H1. rewrite notin_union in H1. destruct H1.
           split~.
  - destruct D2; inversions EQ2.
    cbn in Fr.
    constructor.
    + fold (D1 |,| D2).
      apply~ IHMatch.
    + apply subst_eq_weaken with X T; auto.
      lets FM: subst_has_no_fv Match.
      introv Ain.
      eapply FM.
      apply List.in_or_app; left. apply Ain.
Qed.

Lemma equation_weaken_var:
  forall (Σ : GADTEnv) (D1 D2 : list typctx_elem) (Y : var) (T1 T2 : typ),
    entails_semantic Σ (D1 |,| D2) (T1 ≡ T2) ->
    Y \notin fv_delta D2 ->
    entails_semantic Σ ((D1 |,| [tc_var Y]) |,| D2) (T1 ≡ T2).
Proof.
  introv Sem YFr.
  cbn in *.
  introv M.
  lets [Θ1 [Θ2 [U [EQ [M1 [S1 S2]]]]]]: subst_match_decompose_var M; subst.
  lets M2: subst_match_remove_unused_var M YFr.
  lets EQ: Sem M2.
  fold_delta.
  apply* subst_eq_strengthen_gen.
Qed.

Lemma typing_weakening_delta_eq:
  forall (u : trm) (Σ : GADTEnv) (D1 D2 : list typctx_elem) (E : env bind) (U : typ) eq TT,
    {Σ, D1 |,| D2, E} ⊢(TT) u ∈ U ->
    {Σ, D1 |,| [tc_eq eq] |,| D2, E} ⊢(TT) u ∈ U.
Proof.
  introv Typ; gen_eq D': (D1 |,| D2); gen D2.
  induction Typ; introv EQ; subst;
    try solve [
          econstructor; fresh_intros; eauto
        | econstructor; eauto using okt_weakening_delta_eq; eauto using wft_weaken
        ].
  - apply_fresh typing_tabs as Y; auto.
    lets* IH: H1 Y (D2 |,| [tc_var Y]).
  - econstructor; eauto.
    introv In Alen Adist Afr xfr xAfr.

    lets* IH: H4 In xAfr (D2 |,| tc_vars Alphas |,|
                          equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def))).
    repeat rewrite List.app_assoc in *.
    apply~ IH.
  - econstructor; eauto.
    + destruct eq. apply~ equation_weaken_eq.
    + apply~ wft_weaken.
Qed.

Lemma typing_weakening_delta:
  forall (u : trm) (Σ : GADTEnv) (D1 D2 : list typctx_elem) (E : env bind) (U : typ) (Y : var) TT,
    {Σ, D1 |,| D2, E} ⊢(TT) u ∈ U ->
    Y # E ->
    Y \notin domΔ D1 ->
    Y \notin domΔ D2 ->
    Y \notin fv_delta D2 ->
    {Σ, D1 |,| [tc_var Y] |,| D2, E} ⊢(TT) u ∈ U.
Proof.
  introv Typ FE FD1 FD2 FrD; gen_eq D': (D1 |,| D2); gen D2.
  lets Typ2: Typ.
  induction Typ; introv FD2 FrD EQ; subst;
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
    introv Hin.
    try let envvars := gather_vars in
    introv Hlen Hdist Afresh xfreshL xfreshA;
      instantiate (1:=envvars) in xfreshL.
    lets IH: H4 Hin Hlen (D2 |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def))); eauto.
    + introv Ain. lets*: Afresh Ain.
    + eauto.
    + apply~ H3.
      introv Ain. lets*: Afresh Ain.
    + repeat rewrite List.app_assoc in *.
      apply IH; auto.
      rewrite notin_domΔ_eq; split; auto.
      * rewrite notin_domΔ_eq; split; auto.
        -- apply notin_dom_tc_vars.
           intro HF.
           lets HF2: from_list_spec HF.
           lets HF3: LibList_mem HF2.
           lets HF4: Afresh HF3.
           eapply notin_same.
           instantiate (1:=Y).
           eauto.
        -- rewrite equations_have_no_dom; auto.
           apply* equations_from_lists_are_equations.
      * repeat rewrite fv_delta_app.
        repeat rewrite notin_union.
        splits~.
        -- rewrite~ fv_delta_alphas.
        -- lets [? [? WFT]]: typing_regular Typ.
           lets FV: wft_gives_fv WFT.
           cbn in FV.
           apply fv_delta_equations.
           ++ intros T Tin.
              intro HF.
              lets FV2: fold_left_subset fv_typ Tin.
              lets FV3: subset_transitive FV2 FV.
              lets FV4: FV3 HF.
              rewrite domDelta_app in FV4.
              rewrite in_union in FV4.
              destruct FV4; auto.
           ++ intros R Rin.
              assert (OKS: okGadt Σ).
              ** apply~ okt_implies_okgadt.
                 apply* typing_regular.
              ** destruct OKS as [? OKS].
                 lets [? OKD]: OKS H0.
                 lets Din: fst_from_zip Hin.
                 lets OKC: OKD Din.
                 inversion OKC as [? ? ? ? ? ? ? ? ? FrR]; subst.
(*                  lets FrEQ: FrR Rin.
                 rewrite FrEQ. auto. *)
                 admit.
  - econstructor.
    + apply~ IHTyp.
    + apply~ equation_weaken_var.
    + apply wft_weaken.
      lets~ [? [? ?]]: typing_regular Typ2.
Admitted.

Lemma typing_weakening_delta_many_eq : forall Σ Δ E Deqs u U TT,
    {Σ, Δ, E} ⊢(TT) u ∈ U ->
    (forall eq, List.In eq Deqs -> exists ϵ, eq = tc_eq ϵ) ->
    {Σ, Δ |,| Deqs, E} ⊢(TT) u ∈ U.
  induction Deqs; introv Typ EQs.
  - clean_empty_Δ. auto.
  - destruct a;
      try solve [lets HF: EQs (tc_var A); false~ HF].
    fold_delta.
    rewrite <- List.app_assoc.
    lets W: typing_weakening_delta_eq Σ (Δ |,| Deqs) emptyΔ.
    clean_empty_Δ.
    rewrite <- (List.app_nil_l ((Δ |,| Deqs) |,| [tc_eq eq])).
    apply~ W.
    apply~ IHDeqs.
    intros eq1 ?. lets Hin: EQs eq1.
    destruct Hin; eauto.
    cbn. auto.
Qed.

Lemma typing_weakening_delta_many : forall Σ Δ E As u U TT,
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A \notin domΔ Δ) ->
    DistinctList As ->
    {Σ, Δ, E} ⊢(TT) u ∈ U ->
    {Σ, Δ |,| tc_vars As, E} ⊢(TT) u ∈ U.
  induction As as [| Ah Ats]; introv AE AD Adist Typ.
  - cbn. clean_empty_Δ. auto.
  - cbn. fold_delta.
    inversions Adist.
    rewrite <- (List.app_nil_l ((Δ |,| tc_vars Ats) |,| [tc_var Ah])).
    apply typing_weakening_delta; cbn; auto with listin.
    rewrite notin_domΔ_eq. split.
    + auto with listin.
    + apply notin_dom_tc_vars.
      intro HF.
      apply from_list_spec in HF.
      apply LibList_mem in HF.
      auto.
Qed.

Lemma okt_weakening_delta_many_eq : forall Σ D1 D2 Deqs E,
    okt Σ (D1 |,| D2) E ->
    (forall eq, List.In eq Deqs -> exists ϵ, eq = tc_eq ϵ) ->
    okt Σ (D1 |,| Deqs |,| D2) E.
  induction Deqs; introv Hok Heq.
  - clean_empty_Δ. auto.
  - destruct a.
    + lets: Heq (tc_var A); cbn in *; false* Heq; congruence.
    + fold_delta.
      rewrite <- List.app_assoc.
      apply okt_weakening_delta_eq.
      apply IHDeqs; auto.
      intros eq1 ?. lets Hin: Heq eq1.
      apply Hin. cbn. auto.
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
    apply okt_weakening_delta; auto with listin.
    apply notin_domΔ_eq. split; auto with listin.
    apply notin_dom_tc_vars.
    intro HF.
    apply from_list_spec in HF.
    apply LibList_mem in HF.
    auto.
Qed.

Lemma typing_weakening : forall Σ Δ E F G e T TT,
    {Σ, Δ, E & G} ⊢(TT) e ∈ T ->
    okt Σ Δ (E & F & G) ->
    {Σ, Δ, E & F & G} ⊢(TT) e ∈ T.
Proof.
  introv HTyp. gen_eq K: (E & G). gen G F.
  induction HTyp using typing_ind; introv EQ Ok; subst; eauto.
  - apply* typing_var. apply* binds_weaken.
  - econstructor; eauto.
    let env := gather_vars in
    instantiate (2:=env).
    introv xfresh.
    lets IH: H0 x (G & x ~: V) F; auto.
    rewrite <- concat_assoc.
    apply IH.
    + auto using concat_assoc.
    + rewrite concat_assoc.
      econstructor; eauto.
      assert (xL: x \notin L); auto.
      lets Typ: H xL.
      lets [? [? ?]]: typing_regular Typ.
      eapply okt_is_wft. eauto.
  - apply_fresh* typing_tabs as X.
    lets IH: H1 X G F; auto.
    apply IH.
    + auto using JMeq_from_eq.
    + rewrite <- (List.app_nil_l (Δ |,| [tc_var X])).
      apply okt_weakening_delta; clean_empty_Δ; cbn; auto.
  - apply_fresh* typing_fix as x.
    lets IH: H1 x (G & x ~: T) F; auto.
    rewrite <- concat_assoc.
    apply IH; repeat rewrite concat_assoc; auto.
    constructor; auto.
    lets [? [? ?]]: typing_regular T; eauto.
  - apply_fresh* typing_let as x.
    lets IH: H0 x (G & x ~: V) F; auto.
    rewrite <- concat_assoc.
    apply IH; repeat rewrite concat_assoc; auto.
    constructor; auto.
    lets [? [? ?]]: typing_regular V; eauto.
  - eapply typing_case; eauto.
    introv Inzip.
    let envvars := gather_vars in
    (introv AlphasArity ADistinct Afresh xfresh xfreshA;
     instantiate (1:=envvars) in Afresh).
    assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
      [ introv Ain; lets*: Afresh Ain | idtac ].
    assert (xfreshL: x \notin L); eauto.
    lets* IH1: H4 Inzip Alphas x AlphasArity ADistinct.
    lets* IH2: IH1 AfreshL xfreshL xfreshA (G & x ~: open_tt_many_var Alphas (Cargtype def)) F.
    repeat rewrite concat_assoc in IH2.
    apply~ IH2.

    constructor; auto.
    + rewrite <- (List.app_nil_l (Δ |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def)))).
      apply okt_weakening_delta_many_eq.
      * apply okt_weakening_delta_many; clean_empty_Δ;
          try solve [introv Ain; cbn; lets: Afresh Ain; auto]; auto.
      * apply* equations_from_lists_are_equations.
    + assert (OKS: okGadt Σ).
      * apply~ okt_implies_okgadt.
        apply* typing_regular.
      * destruct OKS as [? OKS].
        lets [? OKD]: OKS H0.
        lets Din: fst_from_zip Inzip.
        lets OKC: OKD Din.
        inversion OKC as [? ? ? ? ? ? Harg ? ? ?]; subst.
        cbn.
        apply wft_weaken_simple.
        apply~ Harg.
    + repeat rewrite notin_domΔ_eq.
      split~.
      * split~.
        apply notin_dom_tc_vars. auto.
      * rewrite equations_have_no_dom; eauto using equations_from_lists_are_equations.
Qed.

(* Hint Resolve typing_implies_term wft_strengthen okt_strengthen. *)

Lemma typing_through_subst_ee : forall Σ Δ E F x u U e T TT1 TT2,
    {Σ, Δ, E & (x ~: U) & F} ⊢(TT1) e ∈ T ->
    {Σ, Δ, E} ⊢(TT2) u ∈ U ->
    {Σ, Δ, E & F} ⊢(Tgen) subst_ee x u e ∈ T.
  Ltac apply_ih :=
    match goal with
    | H: forall X, X \notin ?L -> forall E0 F0 x0 U0, ?P1 -> ?P2 |- _ =>
      apply_ih_bind* H end.
  introv TypT TypU.
  inductions TypT; introv; cbn;
    try solve [eapply Tgen_from_any; eauto using okt_strengthen];
    lets [okU [termU wftU]]: typing_regular TypU.
  - match goal with
    | [ H: okt ?A ?B ?C |- _ ] =>
      lets: okt_strengthen H
    end.
    case_var.
    + eapply Tgen_from_any. binds_get H. eauto.
      assert (E & F & empty = E & F) as HEF. apply concat_empty_r.
      rewrite <- HEF.
      apply typing_weakening; rewrite concat_empty_r; eauto.
    + eapply Tgen_from_any. binds_cases H; apply* typing_var.
  - eapply Tgen_from_any.
    apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    apply_fresh* typing_tabs as Y; rewrite* subst_ee_open_te_var.
    match goal with
    | [ H: forall X, X \notin ?L -> forall E0 F0 x0 U0, ?P1 -> ?P2 |- _ ] =>
      apply* H
    end.
    rewrite <- (List.app_nil_l (Δ |,| [tc_var Y])).
    apply typing_weakening_delta; clean_empty_Δ; cbn; auto.
  - eapply Tgen_from_any.
    apply_fresh* typing_fix as y; rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    apply_fresh* typing_let as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih.
  - eapply Tgen_from_any.
    econstructor; eauto.
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

      assert (Htypfin: {Σ, Δ |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def)),
                        E & F & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))}
                ⊢(Tgen) subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause) ∈ Tc).
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
        apply typing_weakening_delta_many_eq;
          eauto using equations_from_lists_are_equations.
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

Lemma okt_strengthen_simple_delta : forall Σ Δ E Z,
    okt Σ (Δ |,| [tc_var Z]) E ->
    Z # E ->
    Z \notin fv_env E ->
    okt Σ Δ E.
  intros.
  rewrite <- (List.app_nil_l Δ).
  eapply okt_strengthen_delta_var with Z; auto.
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
    rewrite List.app_assoc in *.
    apply~ IH.
    rewrite <- List.app_assoc.
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

Definition subst_td (A : var) (U : typ) (d : typctx_elem) : typctx_elem :=
  match d with
  | tc_var A => tc_var A
  | tc_eq (T1 ≡ T2) => tc_eq ((subst_tt A U T1) ≡ (subst_tt A U T2))
  end.

Fixpoint subst_td_many (Xs : list var) (Us : list typ) (d : typctx_elem) : typctx_elem :=
  match (Xs, Us) with
  | ((List.cons X Xt), (List.cons U Ut)) => subst_td_many Xt Ut (subst_td X U d)
  | _ => d
  end.

(* This lemma is very WIP *)
Lemma okt_strengthen_delta_var_subst_new : forall Σ D1 D2 E X P,
    wft Σ D1 P ->
    okt Σ (D1 |,| [tc_var X] |,| D2) E ->
    X # E ->
    okt Σ (D1 |,| List.map (subst_td X P) D2) (map (subst_tb X P) E).
  introv WFT OKT.
  gen_eq G: (D1 |,| [tc_var X] |,| D2). gen D2 X.
  induction OKT; introv Heq XE; subst.
  - rewrite map_empty.
    econstructor; auto.
  - rewrite map_concat.
    rewrite map_single.
    constructor; auto.
    + apply* wft_subst_tb_2.
      * admit.
      * apply~ wft_weaken_simple.
    + repeat (apply notin_domΔ_eq in H1; destruct H1).
      apply notin_domΔ_eq; split~.
      admit.
Admitted.

(* WIP: new statement of the lemma, accounting substituting stuff inside equations *)
Lemma typing_through_subst_te:
  forall Σ Δ1 Δ2 E Z e P T TT,
    {Σ, Δ1 |,| [tc_var Z] |,| Δ2, E} ⊢(TT) e ∈ T ->
    wft Σ (Δ1 |,| Δ2) P ->
    Z \notin fv_typ P ->
    Z # E ->
    {Σ, Δ1 |,| List.map (subst_td Z P) Δ2, map (subst_tb Z P) E} ⊢(Tgen) subst_te Z P e ∈ subst_tt Z P T.
Proof.
  (* introv Typ. gen_eq G: (Δ1 |,| [tc_var Z] |,| Δ2). gen Δ2. *)
  (* induction Typ; introv GEQ Hwft FPZ FPE; subst; *)
  (*   try match goal with *)
  (*       | [ H: okt Σ (Δ1 |,| [tc_var Z] |,| ?Δ2) E |- _ ] => *)
  (*           lets Hokt2: okt_strengthen_delta_var_subst P H *)
  (*   end; *)
  (*   cbn; auto; *)
  (*     try solve [ *)
  (*           apply Tgen_from_any with Treg; *)
  (*           econstructor; lets*: IHTyp Hwft FPE *)
  (*         | apply Tgen_from_any with Treg; eauto *)
  (*         ]. *)
  (* - apply Tgen_from_any with Treg. *)
  (*   econstructor; auto. *)
  (*   fold (subst_tb Z P (bind_var T)). *)
  (*   apply* binds_map. *)
  (* - assert (Hokconstr: okConstructorDef Σ Tarity (mkGADTconstructor (length Ts) CargType CretTypes)). *)
  (*   + apply* gadt_constructor_ok. apply* okt_implies_okgadt. *)
  (*     lets*: typing_regular Typ. *)
  (*   + inversion Hokconstr *)
  (*       as [? ? ? ? ? Harity Warg Wret Farg Fret]; subst. *)
  (*     apply Tgen_from_any with Treg. *)
  (*     econstructor; eauto. *)
  (*     * apply* List.map_length. *)
  (*     * apply* subst_commutes_open_tt_many. *)
  (*       rewrite Farg. eauto. *)
  (*     * introv Timaped. *)
  (*       lets* Hinmap: List.in_map_iff (subst_tt Z P) Ts T. *)
  (*       apply Hinmap in Timaped. *)
  (*       destruct Timaped as [T' [Teq T'in]]. *)
  (*       subst. *)
  (*       apply* wft_subst_tb_2. *)
  (*     * apply* subst_commutes_open_tt_many. *)
  (*       cbn. rewrite* fold_empty. *)
  (* - apply Tgen_from_any with Treg. *)
  (*   apply_fresh* typing_abs as x. *)
  (*   rewrite subst_te_open_ee_var. *)
  (*   fold (subst_tb Z P (bind_var V)). *)
  (*   rewrite <- map_single. *)
  (*   rewrite <- map_concat. *)
  (*   apply H0; auto. *)
  (* - apply Tgen_from_any with Treg. *)
  (*   apply_fresh* typing_tabs as X. *)
  (*   + rewrite* subst_te_open_te_var. *)
  (*   + lets IH: H1 X (Δ2 |,| [tc_var X]); auto. *)
  (*     rewrite List.app_assoc in *. *)
  (*     rewrite* subst_tt_open_tt_var. *)
  (*     rewrite* subst_te_open_te_var. *)
  (*     apply~ IH. *)
  (*     rewrite <- List.app_assoc. *)
  (*     apply* wft_weaken_simple. *)
  (* - apply Tgen_from_any with Treg. *)
  (*   rewrite* subst_tt_open_tt. apply* typing_tapp. *)
  (*   apply* wft_subst_tb_2. *)
  (* - apply Tgen_from_any with Treg. *)
  (*   apply_fresh* typing_fix as y. *)
  (*   rewrite* subst_te_open_ee_var. *)
  (*   unsimpl (subst_tb Z P (bind_var T)). *)
  (*   rewrite* subst_te_open_ee_var. *)
  (*   rewrite <- map_single. *)
  (*   rewrite <- map_concat. *)
  (*   apply* H1. *)
  (* - apply Tgen_from_any with Treg. *)
  (*   apply_fresh* typing_let as y. *)
  (*   unsimpl (subst_tb Z P (bind_var V)). *)
  (*   rewrite* subst_te_open_ee_var. *)
  (*   rewrite <- map_single. *)
  (*   rewrite <- map_concat. *)
  (*   apply* H0. *)
  (* - apply Tgen_from_any with Treg. *)
  (*   apply_fresh* typing_case as x. *)
  (*   + unfold map_clause_trm_trm. *)
  (*     rewrite* List.map_length. *)
  (*   + introv inzip. *)
  (*     lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip. *)
  (*     lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped. *)
  (*     destruct clause as [clA clT]. cbn. *)
  (*     inversions Hclsubst. *)
  (*     lets* Hzip: Inzip_from_nth_error Hdefs Hclin. *)
  (*     lets*: H2 Hzip. *)
  (*   + fold (subst_tt). *)
  (*     introv inzip. *)
  (*     intros Alphas xClause Alen Adist Afresh xfresh xfreshA. *)

  (*     lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip. *)
  (*     lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped. *)
  (*     destruct clause as [clA clT]. cbn. *)
  (*     inversions Hclsubst. *)

  (*     lets* Hzip: Inzip_from_nth_error Hdefs Hclin. *)
  (*     lets* IH: H4 Hzip. *)
  (*     cbn in IH. *)

  (*     assert (Htypfin: {Σ, Δ1 |,| Δ2 |,| tc_vars Alphas |,| equations_from_lists Ts (Crettypes def), *)
  (*                       map (subst_tb Z P) E & *)
  (*                          xClause ~ bind_var (subst_tt Z P (open_tt_many_var Alphas (Cargtype def)))} *)
  (*                        ⊢(Tgen) subst_te Z P (open_te_many_var Alphas clT' open_ee_var xClause) *)
  (*                        ∈ subst_tt Z P Tc). *)
  (*     * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L); *)
  (*         [ introv Ain; lets*: Afresh Ain | idtac ]. *)
  (*       assert (xfreshL: xClause \notin L); eauto. *)
  (*       lets Htmp: IH Alphas xClause Alen Adist AfreshL. *)
  (*       lets Htmp2: Htmp xfreshL xfreshA. *)
  (*       lets Htmp3: Htmp2 (Δ2 |,| tc_vars Alphas |,| equations_from_lists Ts (Crettypes def)). *)
  (*       autorewrite with rew_env_map in Htmp3. *)
  (*       cbn in Htmp3. *)
  (*       repeat rewrite <- List.app_assoc in Htmp3. *)
  (*       repeat rewrite <- List.app_assoc. *)
  (*       apply Htmp3; try rewrite List.app_assoc; auto. *)
  (*       apply* wft_weaken_simple. *)
  (*     * rewrite (@subst_tt_fresh _ _ (open_tt_many_var Alphas (Cargtype def))) in Htypfin. *)
  (*       2: { *)
  (*         lets [Hokt ?]: typing_regular Typ. *)
  (*         lets okgadt: okt_implies_okgadt Hokt. *)
  (*         unfold okGadt in okgadt. *)
  (*         destruct okgadt as [okΣ okCtors]. *)
  (*         lets [defsNe okDefs]: okCtors H0. *)
  (*         lets indef: fst_from_zip Hzip. *)
  (*         lets okCtor: okDefs indef. *)
  (*         inversions okCtor. *)
  (*         cbn. *)
  (*         lets Hsub: fv_smaller_many Alphas argT. *)
  (*         lets snsu: split_notin_subset_union Z Hsub. *)
  (*         apply snsu. *)
  (*         - rewrite H8. eauto. *)
  (*         - intro Zin. *)
  (*           lets [A [Ain Aeq]]: in_from_list Zin. *)
  (*           subst. *)
  (*           lets: Afresh Ain. *)
  (*           assert (Hfalse: A \notin \{A}); eauto. *)
  (*           apply Hfalse. *)
  (*           apply in_singleton_self. *)
  (*       } *)
  (*       assert (Horder: *)
  (*                 open_te_many_var Alphas (subst_te Z P clT') open_ee_var xClause *)
  (*                 = *)
  (*                 subst_te Z P (open_te_many_var Alphas clT' open_ee_var xClause)). *)
  (*       1: { *)
  (*         rewrite* <- subst_commutes_with_unrelated_opens_te_te. *)
  (*         - rewrite* subst_te_open_ee_var. *)
  (*         - intros A Ain. *)
  (*           intro. subst. *)
  (*           lets: Afresh Ain. *)
  (*           assert (HF: Z \notin \{Z}); eauto. *)
  (*           apply HF. apply in_singleton_self. *)
  (*       } *)
  (*       rewrite* Horder. *)
  (*       apply Htypfin. *)
  (*       admit. (* apply Htypfin. *) *)
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

Lemma typing_through_subst_te_2 :
  forall Σ Δ1 Δ2 E Z e P T TT,
    {Σ, Δ1 |,| [tc_var Z] |,| Δ2, E} ⊢(TT) e ∈ T ->
    wft Σ (Δ1 |,| Δ2) P ->
    Z \notin fv_typ P ->
    Z # E ->
    Z \notin fv_env E ->
    {Σ, Δ1 |,| Δ2, E} ⊢(Tgen) subst_te Z P e ∈ subst_tt Z P T.
  (* intros. *)
  (* rewrite <- (@subst_tb_id_on_fresh E Z P); auto with listin. *)
  (* apply* typing_through_subst_te. *)
Admitted.

Lemma typing_through_subst_te_3 :
  forall Σ Δ E Z e P T TT,
    {Σ, Δ |,| [tc_var Z], E} ⊢(TT) e ∈ T ->
    wft Σ Δ P ->
    Z \notin fv_typ P ->
    Z # E ->
    Z \notin fv_env E ->
    {Σ, Δ, E} ⊢(Tgen) subst_te Z P e ∈ subst_tt Z P T.
  (* intros. *)
  (* rewrite <- (@subst_tb_id_on_fresh E Z P); auto with listin. *)
  (* apply* typing_through_subst_te. *)
Admitted.

Lemma typing_through_subst_te_many : forall As Σ Δ Δ2 E F e T Ps TT,
    {Σ, (Δ |,| tc_vars As |,| Δ2), E & F} ⊢(TT) e ∈ T ->
    length As = length Ps ->
    (forall P, List.In P Ps -> wft Σ Δ P) ->
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A # F) ->
    (forall A P, List.In A As -> List.In P Ps -> A \notin fv_typ P) ->
    (forall A, List.In A As -> A \notin fv_env E) ->
    DistinctList As ->
    {Σ, Δ |,| List.map (subst_td_many As Ps) Δ2, E & map (subst_tb_many As Ps) F} ⊢(Tgen) (subst_te_many As Ps e) ∈  subst_tt_many As Ps T.
(*   induction As as [| Ah Ats]; introv Htyp Hlen Pwft AE AF AP AEE Adist; *)
(*     destruct Ps as [| Ph Pts]; try solve [cbn in *; congruence]. *)
(*   - cbn in *. clean_empty_Δ. *)
(*     rewrite map_def. *)
(*     rewrite <- LibList_map. *)
(*     rewrite <- map_id; eauto using Tgen_from_any. *)
(*     intros. destruct x as [? [?]]. *)
(*     cbv. auto. *)
(*   - cbn. *)
(*     inversions Adist. *)
(*     lets IH0: IHAts Σ (Δ) (map (subst_tb Ah Ph) E) (map (subst_tb Ah Ph) F) *)
(*                    (subst_te Ah Ph e). *)
(*     lets IH: IH0 (subst_tt Ah Ph T) Pts. *)
(*     rewrite <- (@subst_tb_id_on_fresh E Ah Ph). *)
(*     rewrite subst_tb_many_split. *)
(*     eapply IH; auto with listin. *)
(*     + lets HT: typing_through_subst_te Σ (Δ |,| (tc_vars Ats)) emptyΔ Ah. *)
(*       rewrite <- map_concat. *)
(*       apply~ HT; clean_empty_Δ; auto with listin. *)
(*       * rewrite List.app_assoc. *)
(*         unfold tc_vars. *)

(*         assert (EQ: (List.map tc_var Ats |,| [tc_var Ah]) = (tc_var Ah :: List.map tc_var Ats)); try solve [cbn; auto]. *)
(*         rewrite EQ. *)
(*         rewrite <- List.map_cons. *)
(*         fold (tc_vars (Ah :: Ats)). *)
(*         eauto. *)
(*       * rewrite <- (List.app_nil_l (Δ |,| tc_vars Ats)). *)
(*         apply wft_weaken. *)
(*         clean_empty_Δ. auto with listin. *)
(*     + lets: fv_env_subst. *)
(*       auto with listin. *)
(*     + auto with listin. *)
  (* Qed. *)
Admitted.

(* TODO: may want to generalize this if necessary *)

Lemma okt_replace_typ : forall Σ Δ E F x T1 T2,
  okt Σ Δ (E & x ~: T1 & F) ->
  wft Σ Δ T2 ->
  okt Σ Δ (E & x ~: T2 & F).
  induction F using env_ind; introv OK WFT.
  - rewrite concat_empty_r.
    rewrite concat_empty_r in OK.
    inversions OK.
    + false* empty_push_inv.
    + apply eq_push_inv in H.
      destruct H as [? [HS ?]]; inversions HS.
      constructor; auto.
  - rewrite concat_assoc in *.
    inversions OK.
    + false* empty_push_inv.
    + apply eq_push_inv in H.
      destruct H as [? [HS ?]]. inversions HS.
      constructor; auto.
      apply* IHF.
Qed.


Ltac generalize_typings :=
  match goal with
  | [ H: {?Σ, ?D, ?E} ⊢(?TT) ?e ∈ ?T |- _ ] =>
    match TT with
    | Tgen => fail 1
    | Treg => fail 1
    | _ => apply Tgen_from_any in H;
           try clear TT
    end
  end.

(* TODO maybe merge with the origl one *)
Lemma okt_is_wft_2 : forall Σ Δ E F x T,
    okt Σ Δ (E & x ~: T & F) -> wft Σ Δ T.
  induction F using env_ind; introv OK.
  - rewrite concat_empty_r in OK.
    apply* okt_is_wft.
  - rewrite concat_assoc in OK.
    inversions OK.
    + false* empty_push_inv.
    + lets (?&?&?): eq_push_inv H. subst.
      apply* IHF.
Qed.

Opaque entails_semantic.
Lemma equations_weaken_match : forall Σ Δ As Ts Us T1 T2,
  List.length Ts = List.length Us ->
  entails_semantic Σ Δ (T1 ≡ T2) ->
  entails_semantic Σ
    (Δ |,| tc_vars As |,| equations_from_lists Ts Us)
    (T1 ≡ T2).
  induction Ts as [| T Ts]; introv Len Sem.
  - cbn.
    induction As as [| A As].
    + cbn. auto.
    + cbn.
      fold (tc_vars As).
      fold_delta.
      rewrite <- (List.app_nil_l (Δ |,| tc_vars As |,| [tc_var A])).
      apply~ equation_weaken_var; cbn; auto.
  - destruct Us as [| U Us].
    + inversion Len.
    + cbn.
      fold (equations_from_lists Ts Us).
      fold_delta.
      rewrite <- (List.app_nil_l (Δ |,| tc_vars As |,| equations_from_lists Ts Us |,| [tc_eq (T ≡ U)])).
      apply equation_weaken_eq.
      rewrite List.app_nil_l.
      apply* IHTs.
Qed.
Transparent entails_semantic.

Lemma typing_replace_typ_gen : forall Σ Δ E F x T1 TT e U T2,
    {Σ, Δ, E & x ~: T1 & F} ⊢( TT) e ∈ U ->
    wft Σ Δ T2 ->
    entails_semantic Σ Δ (T1 ≡ T2) ->
    {Σ, Δ, E & x ~: T2 & F} ⊢(Tgen) e ∈ U.
  introv Typ.
  (* assert (okt Σ Δ (E & x ~: T2 & F)); [admit | idtac]. *)
  gen_eq K: (E & x~: T1 & F). gen F x T1.
  induction Typ using typing_ind; introv EQ WFT Sem; subst; eauto;
    try solve [apply Tgen_from_any with Treg; eauto].
  - apply Tgen_from_any with Treg;
      econstructor. apply* okt_replace_typ.
  - destruct (classicT (x = x0)); subst.
    + lets: okt_is_ok H0.
      apply binds_middle_eq_inv in H; auto.
      inversions H.
      apply typing_eq with T2 Treg.
      * constructor.
        -- apply binds_concat_left.
           ++ apply binds_push_eq.
           ++ lets* [? ?]: ok_middle_inv H1.
        -- apply* okt_replace_typ.
      * apply~ teq_symmetry.
      * apply* okt_is_wft_2.
    + apply Tgen_from_any with Treg.
      constructor.
      * lets [? | [[? [? ?]] | [? [? ?]]]]: binds_middle_inv H; subst.
        -- apply~ binds_concat_right.
        -- false.
        -- apply~ binds_concat_left.
      * apply* okt_replace_typ.
  - apply Tgen_from_any with Treg.
    econstructor.
    introv xiL.
    lets IH: H0 xiL (F & x0 ~: V) x T0.
    repeat rewrite concat_assoc in IH.
    apply* IH.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv xiL.
    lets IH: H1 xiL F x T0.
    repeat rewrite concat_assoc in IH.
    apply* IH.
    + apply~ wft_weaken_simple.
    + rewrite <- (List.app_nil_l (Δ |,| [tc_var X])).
      apply~ equation_weaken_var.
      cbn. auto.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv xiL.
    lets IH: H1 xiL (F & x0 ~: T) x T1.
    repeat rewrite concat_assoc in IH.
    apply* IH.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv xiL.
    lets IH: H0 xiL (F & x0 ~: V) x T1.
    repeat rewrite concat_assoc in IH.
    apply* IH.
  - apply Tgen_from_any with Treg.
    econstructor; eauto.
    introv In Alen Adist Afr xfr xAfr.
    lets Htmp: H4 In Alen Adist Afr xfr.
    lets IH: Htmp xAfr (F & x0 ~: open_tt_many_var Alphas (Cargtype def)) x T1. clear Htmp.
    repeat rewrite concat_assoc in IH.
    apply* IH.
    + repeat apply* wft_weaken_simple.
    + apply~ equations_weaken_match.
      rewrite List.map_length.
      lets [OKT [? WFT2]]: typing_regular Typ.
      inversions WFT2.
      lets OKS: okt_implies_okgadt OKT.
      inversion OKS as [? OKC].
      lets [? OKD]: OKC H0.
      lets indef: fst_from_zip In.
      lets OKE: OKD indef.
      inversions OKE.
      cbn.
      match goal with
      | [ H1: binds ?g ?A Σ, H2: binds ?g ?B Σ |- _ ] =>
        let H := fresh "H" in
        lets H: binds_ext H1 H2;
          inversions H
      end.
      auto.
Qed.

Lemma typing_replace_typ : forall Σ Δ E x T1 TT e U T2,
    {Σ, Δ, E & x ~: T1} ⊢( TT) e ∈ U ->
    entails_semantic Σ Δ (T1 ≡ T2) ->
    wft Σ Δ T2 ->
    {Σ, Δ, E & x ~: T2} ⊢( Tgen) e ∈ U.
  intros.
  rewrite <- (concat_empty_r (E & x ~: T2)).
  apply* typing_replace_typ_gen.
  fold_env_empty.
Qed.

Lemma subst_tt_prime_reduce_arrow : forall O T1 T2,
    subst_tt' (T1 ==> T2) O = subst_tt' T1 O ==> subst_tt' T2 O.
  induction O as [| [A U]]; cbn; auto.
Qed.

(* TODO: move to Equations *)
Lemma inversion_eq_arrow : forall Σ Δ TA1 TB1 TA2 TB2,
    entails_semantic Σ Δ ((TA1 ==> TB1) ≡ (TA2 ==> TB2)) ->
    entails_semantic Σ Δ (TA1 ≡ TA2) /\
    entails_semantic Σ Δ (TB1 ≡ TB2).
  introv Sem; cbn in *.
  split~;
       introv M;
    lets EQ: Sem M;
    repeat rewrite subst_tt_prime_reduce_arrow in EQ;
    inversion~ EQ.
Qed.

Lemma subst_tt_prime_reduce_tuple : forall O T1 T2,
    subst_tt' (T1 ** T2) O = subst_tt' T1 O ** subst_tt' T2 O.
  induction O as [| [A U]]; cbn; auto.
Qed.

Lemma inversion_eq_tuple : forall Σ Δ TA1 TB1 TA2 TB2,
    entails_semantic Σ Δ ((TA1 ** TB1) ≡ (TA2 ** TB2)) ->
    entails_semantic Σ Δ (TA1 ≡ TA2) /\
    entails_semantic Σ Δ (TB1 ≡ TB2).
  introv Sem; cbn in *.
  split~;
       introv M;
    lets EQ: Sem M;
    repeat rewrite subst_tt_prime_reduce_tuple in EQ;
    inversion~ EQ.
Qed.

Lemma subst_tt_prime_reduce_typ_all : forall O T,
    subst_tt' (typ_all T) O = typ_all (subst_tt' T O).
  induction O as [| [A U]]; cbn; auto.
Qed.

Lemma inversion_eq_typ_all : forall Σ Δ T U,
    entails_semantic Σ Δ (typ_all T ≡ typ_all U) ->
    entails_semantic Σ Δ (T ≡ U).
  introv Sem; cbn in *.
  introv M;
    lets EQ: Sem M;
    repeat rewrite subst_tt_prime_reduce_typ_all in EQ;
    inversion~ EQ.
Qed.

(* Lemma inversion_typing_eq_wft : forall Σ Δ E e T TT, *)
(*     {Σ, Δ, E} ⊢(TT) e ∈ T -> *)
(*     exists T', *)
(*       {Σ, Δ, E} ⊢(Treg) e ∈ T' /\ wft Σ Δ T' /\ entails_semantic Σ Δ (T ≡ T'). *)
(*   introv Htyp. *)
(*   lets Htyp2: Htyp. *)
(*   lets [? [? WFT]]: typing_regular Htyp. *)
(*   induction Htyp; *)
(*     try match goal with *)
(*         | [ H: {Σ, Δ, E} ⊢(Treg) ?e ∈ ?T |- _ ] => *)
(*           exists T; split~; split~; auto using teq_reflexivity *)
(*         end. *)
(*   lets* [T' [IHTyp [IHwft IHeq]]]: IHHtyp Htyp. *)
(*   - lets~ [? [? ?]]: typing_regular Htyp. *)
(*   - exists T'. *)
(*     split~; split~. *)
(*     eauto using teq_symmetry, teq_transitivity. *)
(* Qed. *)

  
Lemma subst_ttprim_open_tt : forall O T U,
  (forall A P, List.In (A, P) O -> type P) ->
  subst_tt' (open_tt T U) O
  =
  open_tt (subst_tt' T O) (subst_tt' U O).
  induction O as [| [X P]]; introv TP; cbn; auto.
  rewrite subst_tt_open_tt; eauto with listin.
Qed.

Lemma subst_match_remove_right_var3 : forall Σ D O X U,
    subst_matches_typctx Σ D (O |, (X, U)) ->
    wft Σ emptyΔ U /\ exists D', subst_matches_typctx Σ D' O /\ X \notin substitution_sources O.
  induction D as [| [Z | [V1 V2]]]; introv M.
  - cbn in *.
    inversions M.
  - inversions M.
    splits~.
    eauto.
  - inversions M.
    lets~ IH: IHD H3.
Qed.

Lemma subst_has_wft : forall Σ O Δ,
  subst_matches_typctx Σ Δ O ->
  forall A P, List.In (A, P) O -> wft Σ emptyΔ P.
  induction O as [| [X U]]; introv M.
  - intros. false~.
  - introv Hin.
    cbn in Hin.
    lets* [? [D' ?]]: subst_match_remove_right_var3 M.
    destruct Hin; subst.
    + inversions H1. auto.
    + apply* IHO.
Qed.

Lemma subst_has_closed : forall Σ O Δ,
  subst_matches_typctx Σ Δ O ->
  forall A P, List.In (A, P) O -> type P.
  introv M Hin.
  lets: subst_has_wft M Hin.
  apply* type_from_wft.
Qed.

Lemma teq_open : forall Σ Δ T1 T2 T,
  entails_semantic Σ Δ (T1 ≡ T2) ->
  entails_semantic Σ Δ (open_tt T1 T ≡ open_tt T2 T).
  introv Sem.
  cbn in *.
  introv M.
  lets: subst_has_closed M.
  repeat rewrite~ subst_ttprim_open_tt.
  f_equal.
  apply~ Sem.
Qed.

Lemma subst_tt_prime_reduce_typ_gadt : forall O Ts N,
    subst_tt' (typ_gadt Ts N) O = typ_gadt (List.map (fun T => subst_tt' T O) Ts) N.
  induction O as [| [A U]]; introv; cbn; auto.
  - rewrite~ List.map_id.
  - rewrite IHO.
    f_equal.
    rewrite List.map_map. auto.
Qed.

Lemma lists_map_eq : forall A B (f : A -> B) la lb a b,
    List.map f la = List.map f lb ->
    List.In (a, b) (zip la lb) ->
    f a = f b.
  induction la as [| a' la]; destruct lb as [| b' lb]; introv Map In; try solve [inversion Map | inversion In].
  cbn in *.
  inversions Map.
  destruct In as [In | In].
  - inversions~ In.
  - apply IHla with lb; auto.
Qed.

Lemma inversion_eq_typ_gadt : forall Σ Δ Ts Us N,
    List.length Ts = List.length Us ->
    entails_semantic Σ Δ (typ_gadt Ts N ≡ typ_gadt Us N) ->
    List.Forall2 (fun T U => entails_semantic Σ Δ (T ≡ U)) Ts Us.
  introv Len Sem.
  apply F2_iff_In_zip.
  split~.
  intros T U In.
  cbn in *.
  introv M.
  lets EQ: Sem M.
  repeat rewrite subst_tt_prime_reduce_typ_gadt in EQ.
  inversion EQ as [EQ2].
  lets~ : lists_map_eq EQ2 In.
Qed.

Lemma okt_strengthen_delta_eq : forall Σ D1 D2 E eq,
    okt Σ (D1 |,| [tc_eq eq] |,| D2) E -> okt Σ (D1 |,| D2) E.
  introv OK.
  induction E using env_ind.
  - constructor.
    lets*: okt_implies_okgadt.
  - destruct v as [T].
    inversions OK.
    + lets*: empty_push_inv H.
    + lets [? [? ?]]: eq_push_inv H.
      match goal with
      | H: bind_var ?A = bind_var ?B |- _ => inversions H
      end.
      constructor; auto.
      * apply* wft_strengthen_equation.
      * rewrite notin_domΔ_eq in *; auto.
Qed.

Lemma subst_eq_weaken2 : forall O1 O2 T1 T2 E D,
    subst_matches_typctx E D (O1 |,| O2) ->
    subst_tt' T1 O1 = subst_tt' T2 O1 ->
    subst_tt' T1 (O1 |,| O2) = subst_tt' T2 (O1 |,| O2).
  induction O2 as [| [A U]]; introv M EQ; cbn in *; auto.
  lets [? [D2 ]]: subst_match_remove_right_var3 M.
  apply* IHO2.
  assert (forall (X : var) (U0 : typ), List.In (X, U0) O1 -> A \notin fv_typ U0).
  - admit.
  - assert (A \notin substitution_sources O1).
    + admit.
    + repeat rewrite* subst_tt_inside.
      f_equal.
      auto.
Admitted.

Lemma subst_strengthen_true_eq : forall Σ Δ1 Δ2 O1 O2 U1 U2,
    subst_matches_typctx Σ Δ1 O1 ->
    subst_matches_typctx Σ (Δ1 |,| Δ2) (O1 |,| O2) ->
    subst_tt' U1 O1 = subst_tt' U2 O1 ->
    subst_matches_typctx Σ (Δ1 |,| [tc_eq (U1 ≡ U2)] |,| Δ2) (O1 |,| O2).
  induction Δ2 as [| [| [V1 V2]]]; introv M1 M2 EQ; cbn in *; fold_delta.
  - constructor; auto.
    apply* subst_eq_weaken2.
  - inversions M2.
    destruct O2.
    + cbn in H1. subst.
      econstructor; eauto.
      * admit.
      * admit.
    + inversions H1.
      econstructor; eauto.
      (* TODO continue here *)
  (* this may not work ?? it should *)
Admitted.

Lemma subst_match_split : forall Σ Δ1 Δ2 O,
    subst_matches_typctx Σ (Δ1 |,| Δ2) O ->
    exists O1 O2, O = O1 |,| O2 /\ subst_matches_typctx Σ Δ1 O1.
  induction Δ2; introv M; cbn in *.
  - exists O (@nil (var*typ)). auto.
  - inversions M.
    + lets [O1 [O2 [EQ M2]]]: IHΔ2 H2; subst.
      exists O1 (O2 |, (A, T)).
      auto.
    + apply IHΔ2.
      auto.
Qed.

Lemma equation_strengthen : forall Σ Δ1 Δ2 U1 U2 T1 T2,
    entails_semantic Σ (Δ1 |,| [tc_eq (U1 ≡ U2)] |,| Δ2) (T1 ≡ T2) ->
    entails_semantic Σ Δ1 (U1 ≡ U2) ->
    entails_semantic Σ (Δ1 |,| Δ2) (T1 ≡ T2).
  introv SemT SemU.
  cbn in *.
  fold_delta.
  introv M.
  lets [O1 [O2 [? M2]]]: subst_match_split M; subst.
  lets EQ: SemU M2.
  apply SemT.
  apply~ subst_strengthen_true_eq.
Qed.

Lemma remove_true_equation : forall Σ Δ1 Δ2 E e TT T U1 U2,
    {Σ, Δ1 |,| [tc_eq (U1 ≡ U2)] |,| Δ2, E} ⊢(TT) e ∈ T ->
    entails_semantic Σ Δ1 (U1 ≡ U2) ->
    {Σ, Δ1 |,| Δ2, E} ⊢(TT) e ∈ T.
  introv Typ.
  gen_eq D3: (Δ1 |,| [tc_eq (U1 ≡ U2)] |,| Δ2). gen Δ1 Δ2.
  lets: okt_strengthen_delta_eq.
  lets: wft_strengthen_equation.
  induction Typ using typing_ind; introv EQ Sem; subst; eauto.
  - econstructor; eauto.
    introv XFr.
    lets IH: H3 XFr Δ1 (Δ2 |,| [tc_var X]).
    apply* IH.
  - econstructor; eauto.
    introv clin Hlen Hdist Afresh xfresh xfreshA.
    lets Htmp: H6 clin Hlen Hdist Afresh xfresh.
    lets IH: Htmp xfreshA Δ1
                  (Δ2 |,| tc_vars Alphas |,| equations_from_lists Ts (List.map (open_tt_many_var Alphas) (Crettypes def)));
      clear Htmp.
    repeat rewrite List.app_assoc in *.
    apply* IH.
  - lets: equation_strengthen H1 Sem.
    econstructor; eauto.
Qed.

Lemma remove_true_equations : forall Σ Δ E e TT V Ts Us,
    {Σ, Δ |,| equations_from_lists Ts Us, E} ⊢(TT) e ∈ V ->
    List.Forall2 (fun T U => entails_semantic Σ Δ (T ≡ U)) Ts Us ->
    {Σ, Δ, E} ⊢(TT) e ∈ V.
Admitted.

Lemma helper_equations_commute : forall Ts As Us Vs,
    List.length As = List.length Us ->
    (forall A, List.In A As -> A \notin fv_typs Ts) ->
    equations_from_lists
      Ts
      (List.map (fun T : typ => subst_tt_many As Us (open_tt_many_var As T)) Vs)
    =
    List.map
      (subst_td_many As Us)
      (equations_from_lists Ts (List.map (open_tt_many_var As) Vs)).
  induction As; introv Hlen Afr; destruct Us; try solve [false Hlen].
  - cbn.
    repeat rewrite~ List.map_id.
  - cbn.
Admitted.

Theorem preservation_thm : preservation.
  Ltac find_hopen :=
    let Hopen := fresh "Hopen" in
    match goal with
    | H: forall x, x \notin ?L -> typing _ _ _ _ _ _ |- _ =>
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
      try solve [crush_ihred_gen | eauto using Tgen_from_any];
      repeat generalize_typings.
  - (* app *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp2.
    inversions HT.
    pick_fresh x.
    find_hopen. forwards~ K: (Hopen x).
    rewrite* (@subst_ee_intro x).
    expand_env_empty E.
    apply* typing_through_subst_ee.
    fold_env_empty.
    apply teq_symmetry in EQ.
    lets [EQarg EQret]: inversion_eq_arrow EQ.
    apply typing_eq with T0 Tgen; auto.
    + apply* typing_replace_typ.
      lets*: typing_regular Htyp1.
    + lets* [? [? WFT]]: typing_regular Htyp2.
      inversion~ WFT.
  - (* tabs *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp.
    inversions HT.

    apply teq_symmetry in EQ.
    lets: inversion_eq_typ_all EQ; subst.
    apply typing_eq with (open_tt T0 T) Tgen.
    + pick_fresh X.
      rewrite* (@subst_te_intro X).
      rewrite* (@subst_tt_intro X).
      apply~ typing_through_subst_te_3.
    + apply~ teq_open.
    + lets* [? [? WFT]]: typing_regular Htyp.
      apply~ wft_open.
  - (* fst *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp.
    inversions HT.
    repeat generalize_typings.
    apply teq_symmetry in EQ.
    lets [EQarg EQret]: inversion_eq_tuple EQ.
    apply* typing_eq.
    lets* [? [? WFT]]: typing_regular Htyp.
    inversion~ WFT.
  - (* snd *)
    lets [U [HT EQ]]: inversion_typing_eq Htyp.
    inversions HT.
    repeat generalize_typings.
    apply teq_symmetry in EQ.
    lets [EQarg EQret]: inversion_eq_tuple EQ.
    apply* typing_eq.
    lets* [? [? WFT]]: typing_regular Htyp.
    inversion~ WFT.
  - (* fix *)
    pick_fresh x.
    rewrite* (@subst_ee_intro x).
    expand_env_empty E.
    apply* typing_through_subst_ee.
    fold_env_empty.
  - (* let *)
    pick_fresh x.
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
    rewrite~ (@subst_ee_intro x);
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
    lets [T' [Typ2 EQ]]: inversion_typing_eq Htyp.
    inversions Typ2.
    match goal with
    | [ H1: binds ?g ?A Σ, H2: binds ?g ?B Σ |- _ ] =>
      let H := fresh "H" in
      lets H: binds_ext H1 H2;
        inversions H
    end.
(*     rewrite (@subst_tt_intro_many Alphas _ Ts0) in EQ; auto.
    + admit.
    + 
      [ idtac
      | introv Ain; subst; cbn; cbn in Afresh; lets*: Afresh Ain
      | introv Ain Tin; lets: Afresh Ain; apply* fv_typs_notin
      ]. *)

    rename H20 into TypCtorArg.
    match goal with
    | [ H1: List.nth_error Ctors cid = ?A, H2: List.nth_error Ctors cid = ?B |- _ ] =>
      let H := fresh "H" in
      assert (H: A = B); [ rewrite <- H2; auto | idtac ];
        inversions H
    end.
    rewrite (@subst_tt_intro_many Alphas _ Ts0) in TypCtorArg; auto.
    2: {
      intros A Ain; subst; cbn; cbn in Afresh.
      rewrite H13. auto.
    }
    2: {
      intros A U Ain Uin.
      lets WFT: H29 Uin.
      lets: wft_gives_fv WFT.
      intro HF.
      assert (HA: A \in domΔ Δ); auto.
      lets HA2: Afresh Ain.
      apply HA2. repeat rewrite in_union. repeat right~.
    }

    expand_env_empty E.
    eapply typing_through_subst_ee with (subst_tt_many Alphas Ts0 (open_tt_many_var Alphas CargType)) Tgen _; [ idtac | eauto ].

    (* rewrite (@subst_tt_intro_many Alphas _ Ts0); auto; *)
    (*   [ idtac *)
    (*   | introv Ain; subst; cbn; cbn in Afresh; lets*: Afresh Ain *)
    (*   | introv Ain Tin; lets: Afresh Ain; apply* fv_typs_notin *)
    (*   ]. *)

    (* instantiate the inductive hypothesis *)
    assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
      [ introv Ain; lets*: Afresh Ain | idtac].
    assert (xfreshL: x \notin L); auto.
    assert (xfreshA: x \notin from_list Alphas); auto.

    (* assert (length Alphas = Carity Def); *)
    (*   [ lets Hclarity: H2 Inzip; rewrite <- Hclarity; cbn; trivial | idtac ]. *)
    lets* IH: H3 Inzip Alphas x Adist xfreshA.
    cbn in IH.

    rewrite subst_te_many_commutes_open; auto;
      [ idtac
      | introv Ain; lets: Afresh Ain;
        lets: from_list_spec2 Ain;
        intro; subst; auto
      ].

    fold (subst_tb_many Alphas Ts0 (bind_var (open_tt_many_var Alphas CargType))).
    rewrite <- map_single.
    fold_env_empty.

    rewrite subst_tt_many_free with Alphas Ts0 Tc;
      [ idtac | introv Ain; lets*: Afresh Ain ].

    apply remove_true_equations with Ts (List.map (fun T => subst_tt_many Alphas Ts0 (open_tt_many_var Alphas T)) CretTypes).
    + assert (Hrew:
          equations_from_lists Ts (List.map (fun T : typ => subst_tt_many Alphas Ts0 (open_tt_many_var Alphas T)) CretTypes)
          =
          List.map (subst_td_many Alphas Ts0) (equations_from_lists Ts (List.map (open_tt_many_var Alphas) CretTypes))
        ).
      * apply~ helper_equations_commute.
        introv Ain. lets~ : Afresh Ain.
      * rewrite Hrew; clear Hrew.
        apply typing_through_subst_te_many with Tgen; trivial.
        -- intros A Ain.
           lets: Afresh Ain. auto.
        -- autorewrite with rew_env_dom.
           intros A Ain.
           apply notin_inverse.
           intro HF.
           apply xfreshA.
           rewrite in_singleton in HF. subst.
           apply from_list_spec2. auto.
        -- introv Ain Tin.
           apply fv_typs_notin with Ts0; auto.
           lets: Afresh Ain.
           auto with listin.
        -- introv Ain; lets*: Afresh Ain.
    + assert (Hrew:
                open_tt_many Ts0 (typ_gadt CretTypes Name)
                =
                typ_gadt (List.map (open_tt_many Ts0) CretTypes) Name).
      * clear.
        rename Ts0 into Ts.
        rename CretTypes into Us.
        gen Us.
        induction Ts; introv.
        -- cbn. rewrite~ List.map_id.
        -- cbn. rewrite IHTs.
           f_equal.
           rewrite List.map_map.
           apply List.map_ext.
           intro T. auto.
      * rewrite Hrew in EQ; clear Hrew.
        assert (Hrew: (List.map (fun T : typ => subst_tt_many Alphas Ts0 (open_tt_many_var Alphas T)) CretTypes) = List.map (open_tt_many Ts0) CretTypes).
        1: {
          apply List.map_ext_in.
          intros T Tin.
          rewrite~ <- subst_tt_intro_many.
          - intros A Ain.
            rewrite~ H14.
          - intros A U Ain Uin.
            lets: Afresh Ain.
            apply fv_typs_notin with Ts0; auto.
        }
        rewrite Hrew; clear Hrew.
        lets EQ2: inversion_eq_typ_gadt EQ.
        rewrite <- (List.map_ext_in (fun T : typ => open_tt_many Ts0 T)).
        2: {
          intros T Tin.
          rewrite~ (@subst_tt_intro_many Alphas T Ts0).
          -- rewrite~ H14.
          -- introv Ain Uin. lets HF2: Afresh Ain.
             apply* fv_typs_notin.
        }
        -- rewrite List.map_length.


           lets [OKT [? WFT2]]: typing_regular Htyp.
           inversions WFT2.
           lets OKS: okt_implies_okgadt OKT.
           inversion OKS as [? OKC].
           lets [? OKD]: OKC H0.
           cbn in *.
           lets OKE: OKD indef.
           inversions OKE.
           match goal with
           | [ H1: binds ?g ?A Σ, H2: binds ?g ?B Σ |- _ ] =>
             let H := fresh "H" in
             lets H: binds_ext H1 H2;
               inversions H
           end.
           auto.
        -- apply EQ2.
Qed.
