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

Hint Resolve okt_is_ok.

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

Hint Resolve okt_strengthen_simple.

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

Lemma okt_Alphas_strengthen : forall Σ D E As,
    (forall A, List.In A As -> A # E) ->
    DistinctList As ->
    okt Σ D E ->
    okt Σ (D |,| tc_vars As) E.
  induction As as [| Ah Ats]; introv Afresh Adist Hok.
  (* - cbn. rewrite concat_empty_r. trivial. *)
  (* - cbn. rewrite concat_assoc. *)
  (*   econstructor. *)
  (*   + apply IHAts. *)
  (*     * introv Ain. eauto with listin. *)
  (*     * inversion* Adist. *)
  (*     * trivial. *)
  (*   + rewrite dom_concat. *)
  (*     apply notin_union. constructor. *)
  (*     * eauto with listin. *)
  (*     * inversions Adist. *)
  (*       rewrite add_types_dom_is_from_list. *)
  (*       apply* fromlist_notin_restated. *)
  Admitted.

(* Lemma typing_weakening_delta : forall Σ Δ E F G e T, *)
(*     {Σ, Δ, E & G} ⊢ e ∈ T -> *)
(*     okt Σ Δ (E & F & G) -> *)
(*     {Σ, Δ, E & F & G} ⊢ e ∈ T. *)
(* Proof. *)

Lemma typing_weakening_delta:
  forall (u : trm) (Σ : GADTEnv) (Δ : list typctx_elem) (E : env bind) (U : typ) (Y : var),
    Y # E ->
    Y \notin domΔ Δ ->
    {Σ, Δ, E} ⊢ u ∈ U ->
    {Σ, Δ |,| [tc_var Y], E} ⊢ u ∈ U.
Proof.
Admitted.

Lemma typing_weakening : forall Σ Δ E F G e T,
    {Σ, Δ, E & G} ⊢ e ∈ T ->
    okt Σ Δ (E & F & G) ->
    {Σ, Δ, E & F & G} ⊢ e ∈ T.
Proof.
(*   introv HTyp. gen F. *)
(*   inductions HTyp; introv Ok; eauto. *)
(*   - apply* typing_var. apply* binds_weaken. *)
  (* - econstructor; eauto. *)
  (*   introv Tin. *)
  (*   apply* wft_weaken. *)
  (* - renameIHs IH IHeq. *)
  (*   apply_fresh* typing_abs as x. *)
  (*   forwards~ K: (IH x). *)
  (*   apply_ih_bind (IHeq x); eauto. *)
  (*   econstructor; eauto. *)
  (*   lets (Hokt&?&?): typing_regular K. *)
  (*   lets (?&?&?): okt_push_var_inv Hokt. *)
  (*   apply* wft_weaken. *)
  (* - renameIHs IH IHeq. *)
  (*   apply_fresh* typing_tabs as X. *)
  (*   forwards~ K: (IH X). *)
  (*   apply_ih_bind (IHeq X); auto. *)
  (*   econstructor; eauto. *)
  (* - apply* typing_tapp. apply* wft_weaken. *)
  (* - renameIHs IH IHeq. *)
  (*   apply_fresh* typing_fix as x. *)
  (*   forwards~ K: (IH x). *)
  (*   apply_ih_bind (IHeq x); eauto. *)
  (*   econstructor; eauto. *)
  (*   lets (Hokt&?&?): typing_regular K. *)
  (*   lets (?&?&?): okt_push_var_inv Hokt. *)
  (*   apply* wft_weaken. *)
  (* - renameIHs IH IHeq. *)
  (*   apply_fresh* typing_let as x. *)
  (*   forwards~ K: (IH x). *)
  (*   apply_ih_bind (IHeq x); eauto. *)
  (*   econstructor; eauto. *)
  (*   lets (Hokt&?&?): typing_regular K. *)
  (*   lets (?&?&?): okt_push_var_inv Hokt. *)
  (*   apply* wft_weaken. *)
  (* - apply* typing_case. *)
  (*   let envvars := gather_vars in *)
  (*   (introv Inzip AlphasArity ADistinct Afresh xfresh xfreshA; *)
  (*    instantiate (1:=envvars) in Afresh). *)
  (*   assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L); *)
  (*     [ introv Ain; lets*: Afresh Ain | idtac ]. *)
  (*   assert (xfreshL: x \notin L); eauto. *)
  (*   lets* IH1: H3 Inzip Alphas x AlphasArity ADistinct. *)
  (*   lets* IH2: IH1 AfreshL xfreshL xfreshA. *)
  (*   lets IHeq1: H4 Inzip Alphas x AlphasArity ADistinct. *)
  (*   lets* IHeq2: IHeq1 AfreshL xfreshL xfreshA. *)
  (*   rewrite add_types_assoc. *)

  (*   lets IHeq3: IHeq2 E (add_types G Alphas & x ~ bind_var (open_tt_many_var Alphas (Cargtype def))) F. *)
  (*   + apply JMeq_from_eq. *)
  (*     rewrite add_types_assoc. *)
  (*     rewrite concat_assoc. trivial. *)
  (*   + rewrite concat_assoc in IHeq3. *)
  (*     apply IHeq3. *)
  (*     rewrite <- (concat_empty_r G). *)
  (*     rewrite add_types_assoc. *)
  (*     rewrite concat_assoc. *)
  (*     econstructor. *)
  (*     * apply okt_Alphas_strengthen; trivial. *)
  (*       introv Ain; lets*: Afresh Ain. *)
  (*     * match goal with | H: okt Σ ?E |- _ => lets okgadt: okt_implies_okgadt H end. *)
  (*       unfold okGadt in okgadt. *)
  (*       destruct okgadt as [okΣ okCtors]. *)
  (*       lets [defsNe okDefs]: okCtors H0. *)
  (*       lets indef: fst_from_zip Inzip. *)
  (*       lets okCtor: okDefs indef. *)
  (*       inversions okCtor. *)
  (*       cbn. *)
  (*       rewrite <- add_types_assoc. rewrite concat_empty_r. *)
  (*       lets*: H5 Alphas (E & F & G). *)
  (*     * repeat rewrite dom_concat. *)
  (*       rewrite add_types_dom_is_from_list. *)
  (*       eauto. *)
Admitted.

(* Hint Resolve typing_implies_term wft_strengthen okt_strengthen. *)

Lemma typing_through_subst_ee : forall Σ Δ E F x u U e T,
    {Σ, Δ, E & (x ~: U) & F} ⊢ e ∈ T ->
    {Σ, Δ, E} ⊢ u ∈ U ->
    {Σ, Δ, E & F} ⊢ subst_ee x u e ∈ T.

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
    apply* typing_weakening_delta.
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

      (* assert (Htypfin: {Σ, E &  F Alphas & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))} *)
      (*           ⊢ subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause) ∈ Tc). *)
      (* * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L); *)
      (*     [ introv Ain; lets*: Afresh Ain | idtac ]. *)
      (*   assert (xfreshL: xClause \notin L); eauto. *)
      (*   lets Htmp: IH Alphas xClause Alen Adist AfreshL. *)
      (*   lets Htmp2: Htmp xfreshL xfreshA. *)
      (*   lets Htmp3: Htmp2 E (add_types F Alphas & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))) x U. *)
      (*   cbn in Htmp3. *)
      (*   rewrite <- concat_assoc. *)
      (*   apply* Htmp3. *)
      (*   apply JMeq_from_eq. *)
      (*   rewrite add_types_assoc. eauto using concat_assoc. *)
      (* * rewrite <- add_types_assoc in Htypfin. *)
      (*   assert (Horder: *)
      (*             subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause) *)
      (*             = *)
      (*             open_te_many_var Alphas (subst_ee x u clT') open_ee_var xClause). *)
      (*   -- rewrite* <- subst_ee_open_ee_var. *)
      (*      f_equal. *)
      (*      apply* subst_commutes_with_unrelated_opens_te_ee. *)
      (*   -- rewrite* <- Horder. *)
Admitted.

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

Lemma notin_env_binds:
  forall (Z : var) (E : env bind) (x : var) (T : typ),
    binds x (bind_var T) E ->
    Z \notin fv_env E -> Z \notin fv_typ T.
Proof.
  induction E using env_ind; introv Hbind FE.
  - false* binds_empty_inv.
  - lets [[? ?] | [? ?]]: binds_push_inv Hbind; subst;
      try destruct v; lets* [? ?]: notin_env_inv FE.
Qed.

Lemma okt_strengthen_delta_var_subst : forall Σ D1 D2 E X P,
    X # E ->
    wft Σ (D1 |,| D2) P ->
    okt Σ (D1 |,| [tc_var X] |,| D2) E -> okt Σ (D1 |,| D2) (map (subst_tb X P) E).
Admitted.

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
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

(* Lemma typing_through_subst_te : forall Σ E F Z e T P, *)
(*     {Σ, E & (withtyp Z) & F} ⊢ e ∈ T -> *)
(*     wft Σ E P -> *)
(*     Z \notin fv_typ P -> (* theoretically this assumption should not be needed as it should arise from wft E P /\ okt E + Z (so Z is not in E and P is wft in E so it cannot have free Z), but we can shift this responsibility up *) *)
(*     {Σ, E & map (subst_tb Z P) F} ⊢ (subst_te Z P e) ∈ (subst_tt Z P T). *)
(* Proof. *)
(*   Ltac apply_ih2 := *)
(*     match goal with *)
(*     | H: forall X, X \notin ?L -> forall E0 F0 Z0, ?P1 -> ?P2 |- _ => *)
(*       apply_ih_map_bind* H end. *)
(*   introv Typ W FP. *)
(*   inductions Typ; introv; simpls subst_tt; simpls subst_te; eauto. *)
(*   - apply* typing_var. rewrite* (@map_subst_tb_id Σ E Z P). *)
(*     match goal with *)
(*     | Hbinds: binds _ _ _ |- _ => binds_cases Hbinds; unsimpl_map_bind* end. *)
(*   - assert (Hokconstr: okConstructorDef Σ Tarity (mkGADTconstructor (length Ts) CargType CretTypes)). *)
(*     + apply* gadt_constructor_ok. apply* okt_implies_okgadt. *)
(*       lets*: typing_regular Typ. *)
(*     + inversion Hokconstr *)
(*         as [? ? ? ? ? Harity Warg Wret Farg Fret]; subst. *)
(*       econstructor; eauto. *)
(*       * apply* List.map_length. *)
(*       * apply* subst_commutes_open_tt_many. *)
(*         rewrite Farg. eauto. *)
(*       * introv Timaped. *)
(*         lets* Hinmap: List.in_map_iff (subst_tt Z P) Ts T. *)
(*         apply Hinmap in Timaped. *)
(*         destruct Timaped as [T' [Teq T'in]]. *)
(*         subst. *)
(*         apply* wft_subst_tb. *)
(*         apply* okt_is_ok. *)
(*         apply* okt_strengthen_2. *)
(*         lets* reg: typing_regular Typ. *)
(*       * apply* subst_commutes_open_tt_many. *)
(*         cbn. rewrite* fold_empty. *)
(*   - apply_fresh* typing_abs as y. *)
(*     unsimpl (subst_tb Z P (bind_var V)). *)
(*     rewrite* subst_te_open_ee_var. *)
(*     apply_ih2. *)
(*   - apply_fresh* typing_tabs as Y. *)
(*     + rewrite* subst_te_open_te_var. *)
(*     + unsimpl (subst_tb Z P bind_typ). *)
(*       rewrite* subst_tt_open_tt_var. *)
(*       rewrite* subst_te_open_te_var. *)
(*       apply_ih2. *)
(*   - rewrite* subst_tt_open_tt. apply* typing_tapp. *)
(*     apply* wft_subst_tb. *)
(*     apply* ok_concat_map. *)
(*     destructs (typing_regular Typ). *)
(*     match goal with *)
(*     | Hokt: okt _ _ |- _ => *)
(*       lets*: okt_is_ok Hokt end. *)
(*   - apply_fresh* typing_fix as y. *)
(*     rewrite* subst_te_open_ee_var. *)
(*     unsimpl (subst_tb Z P (bind_var T)). *)
(*     rewrite* subst_te_open_ee_var. *)
(*     apply_ih2. *)
(*   - apply_fresh* typing_let as y. *)
(*     unsimpl (subst_tb Z P (bind_var V)). *)
(*     rewrite* subst_te_open_ee_var. *)
(*     apply_ih2. *)
(*   - eapply typing_case; eauto. *)
(*     + unfold map_clause_trm_trm. *)
(*       rewrite* List.map_length. *)
(*     + introv inzip. *)
(*       lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip. *)
(*       lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped. *)
(*       destruct clause as [clA clT]. cbn. *)
(*       inversions Hclsubst. *)
(*       lets* Hzip: Inzip_from_nth_error Hdefs Hclin. *)
(*       lets*: H2 Hzip. *)
(*     + introv inzip. *)
(*       let env := gather_vars in *)
(*       intros Alphas xClause Alen Adist Afresh xfresh xfreshA; *)
(*         instantiate (1:=env) in xfresh. *)

(*       lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip. *)
(*       lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped. *)
(*       destruct clause as [clA clT]. cbn. *)
(*       inversions Hclsubst. *)

(*       lets* Hzip: Inzip_from_nth_error Hdefs Hclin. *)
(*       lets* IH: H4 Hzip. *)
(*       cbn in IH. *)

(*       assert (Htypfin: {Σ, add_types (E & map (subst_tb Z P) F) Alphas & *)
(*                            xClause ~ bind_var (subst_tt Z P (open_tt_many_var Alphas (Cargtype def)))} *)
(*                          ⊢ subst_te Z P (open_te_many_var Alphas clT' open_ee_var xClause) *)
(*                          ∈ subst_tt Z P Tc). *)
(*       * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L); *)
(*           [ introv Ain; lets*: Afresh Ain | idtac ]. *)
(*         assert (xfreshL: xClause \notin L); eauto. *)
(*         lets Htmp: IH Alphas xClause Alen Adist AfreshL. *)
(*         lets Htmp2: Htmp xfreshL xfreshA. *)
(*         lets Htmp3: Htmp2 E (add_types F Alphas & *)
(*                              xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))) Z. *)
(*         rewrite add_types_assoc. *)
(*         rewrite <- concat_assoc. *)
(*         rewrite add_types_through_map in Htmp3. *)
(*         autorewrite with rew_env_map in Htmp3. *)
(*         cbn in Htmp3. *)
(*         apply* Htmp3. *)
(*         apply JMeq_from_eq. *)
(*         rewrite add_types_assoc. eauto using concat_assoc. *)
(*       * rewrite (@subst_tt_fresh _ _ (open_tt_many_var Alphas (Cargtype def))) in Htypfin. *)
(*         2: { *)
(*           lets [Hokt ?]: typing_regular Typ. *)
(*           lets okgadt: okt_implies_okgadt Hokt. *)
(*           unfold okGadt in okgadt. *)
(*           destruct okgadt as [okΣ okCtors]. *)
(*           lets [defsNe okDefs]: okCtors H0. *)
(*           lets indef: fst_from_zip Hzip. *)
(*           lets okCtor: okDefs indef. *)
(*           inversions okCtor. *)
(*           cbn. *)
(*           lets Hsub: fv_smaller_many Alphas argT. *)
(*           lets snsu: split_notin_subset_union Z Hsub. *)
(*           apply snsu. *)
(*           - rewrite H8. eauto. *)
(*           - intro Zin. *)
(*             lets [A [Ain Aeq]]: in_from_list Zin. *)
(*             subst. *)
(*             lets: Afresh Ain. *)
(*             assert (Hfalse: A \notin \{A}); eauto. *)
(*             apply Hfalse. *)
(*             apply in_singleton_self. *)
(*         } *)
(*         assert (Horder: *)
(*                   open_te_many_var Alphas (subst_te Z P clT') open_ee_var xClause *)
(*                   = *)
(*                   subst_te Z P (open_te_many_var Alphas clT' open_ee_var xClause)). *)
(*         1: { *)
(*           rewrite* <- subst_commutes_with_unrelated_opens_te_te. *)
(*           - rewrite* subst_te_open_ee_var. *)
(*           - intros A Ain. *)
(*             intro. subst. *)
(*             lets: Afresh Ain. *)
(*             assert (HF: Z \notin \{Z}); eauto. *)
(*             apply HF. apply in_singleton_self. *)
(*         } *)
(*         rewrite* Horder. *)
(* Qed. *)

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

Definition subst_tb_many (As : list var) (Ps : list typ) (b : bind) : bind :=
  match b with
  | bind_var T => bind_var (subst_tt_many As Ps T)
  end.

Lemma subst_tb_id_on_fresh : forall E Z P,
    Z \notin fv_env E ->
    map (subst_tb Z P) E = E.
  induction E using env_ind; introv FE.
  - rewrite map_empty. trivial.
  - rewrite map_push.
    destruct v.
    rewrite fv_env_extend in FE.
    f_equal.
    + apply* IHE.
    + cbn.
      f_equal. f_equal.
      apply subst_tt_fresh. auto.
Qed.

Lemma LibList_map : forall T U (l : list T) (f : T -> U),
    List.map f l = LibList.map f l.
  induction l; intros; cbn in *; auto.
  rewrite IHl. fold (LibList.map f l). auto.
Qed.

Lemma subst_tt_many_id_on_fresh : forall T As Ps,
    (forall A, List.In A As -> A \notin fv_typ T) ->
    subst_tt_many As Ps T = T.
  induction As; destruct Ps; intros; try solve [cbn in *; congruence].
  cbn.
  rewrite subst_tt_fresh.
  - apply IHAs; auto with listin.
  - auto with listin.
Qed.

Lemma subst_tb_many_id_on_fresh_env : forall E As Ps,
    length As = length Ps ->
    (forall A, List.In A As -> A \notin fv_env E) ->
    map (subst_tb_many As Ps) E = E.
  intros.
  rewrite map_def.
  rewrite <- LibList_map.
  symmetry.
  rewrite <- map_id; auto.
  intros vb xin.
  destruct vb. cbn.
  f_equal; auto.
  unfold subst_tb_many. destruct b.
  rewrite subst_tt_many_id_on_fresh; auto.
  intros.
  induction E as [| B E].
  - contradiction.
  - lets HA: H0 H1.
    cbn in HA. fold (fv_env E) in HA.
    lets [? | ?]: List.in_inv xin; subst; cbn in HA; auto.
    apply IHE; auto.
    intros A' Ain.
    lets HA': H0 Ain.
    destruct B; destruct b; cbn in HA'. fold (fv_env E) in HA'.
    auto.
Qed.

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

Lemma typing_through_subst_te_many : forall As Σ Δ E e T Ps,
    {Σ, (Δ |,| tc_vars As), E} ⊢ e ∈ T ->
    length As = length Ps ->
    (forall P, List.In P Ps -> wft Σ Δ P) ->
    (forall A, List.In A As -> A # E) ->
    (forall A P, List.In A As -> List.In P Ps -> A \notin fv_typ P) ->
    (forall A, List.In A As -> A \notin fv_env E) ->
    DistinctList As ->
    {Σ, Δ, map (subst_tb_many As Ps) E} ⊢ (subst_te_many As Ps e) ∈  subst_tt_many As Ps T.
  induction As as [| Ah Ats]; introv Htyp Hlen Pwft AE AF AP Adist;
    destruct Ps as [| Ph Pts]; try solve [cbn in *; congruence].
  - rewrite* subst_tb_many_id_on_fresh_env.
    cbn in *. clean_empty_Δ. auto.
  - cbn.
    inversions Adist.
    (* TODO continue here *)
    apply IHAts; auto with listin.
    apply typing_through_subst_te_2; auto with listin.
    + cbn in Htyp. fold (tc_vars Ats) in Htyp.
      fold_delta.
      rewrite <- (List.app_assoc).
      auto.
    + rewrite <- (List.app_nil_r (Δ |,| tc_vars Ats)).
      apply wft_weaken.
      clean_empty_Δ. auto with listin.
Admitted.

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
    rewrite length_equality in Hlen.
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

    (* fold (subst_tb_many Alphas Ts0 (bind_var (open_tt_many_var Alphas (Cargtype Def)))). *)
    (* rewrite <- map_single. *)
    (* fold_env_empty. *)

    rewrite subst_tt_many_free with Alphas Ts0 Tc;
      [ idtac | introv Ain; lets*: Afresh Ain ].
    rewrite (subst_tb_id_on_fresh

    apply typing_through_subst_te_many; trivial.
    + app;ly
    + rewrite <- add_types_assoc.
      rewrite* concat_empty_r.
    + inversions Htyp.
      auto with listin.
    + introv Ain; lets*: Afresh Ain.
    + autorewrite with rew_env_dom.
      introv Ain.
      intro HF. rewrite in_singleton in HF. subst.
      apply xfreshA.
      apply* from_list_spec2.
    + introv Ain Tin; lets: Afresh Ain; apply* fv_typs_notin.
Admitted.

