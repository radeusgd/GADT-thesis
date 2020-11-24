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

Lemma add_types_assoc : forall E F As,
    add_types (E & F) As = E & add_types F As.
  induction As; cbn; eauto.
  - rewrite IHAs. eauto using concat_assoc.
Qed.

Lemma add_types_dom_is_from_list : forall As,
    dom (add_types empty As) = from_list As.
  induction As; cbn.
  - apply dom_empty.
  - rewrite dom_concat.
    rewrite IHAs.
    rewrite union_comm.
    unfold from_list.
    rewrite dom_single.
    trivial.
Qed.

Lemma fromlist_notin_restated : forall T (X : T) As,
    ~ List.In X As ->
    X \notin from_list As.
  induction As as [|Ah Ats]; introv Hnotin.
  - cbn. eauto.
  - cbn.
    rewrite notin_union.
    constructor.
    + apply notin_singleton.
      intro HF. subst.
      apply Hnotin. eauto with listin.
    + unfold from_list in IHAts.
      apply* IHAts.
      intro HF.
      apply Hnotin. eauto with listin.
Qed.

Lemma okt_Alphas_strengthen : forall Σ E As,
    (forall A, List.In A As -> A # E) ->
    DistinctList As ->
    okt Σ E ->
    okt Σ (E & add_types empty As).
  induction As as [| Ah Ats]; introv Afresh Adist Hok.
  - cbn. rewrite concat_empty_r. trivial.
  - cbn. rewrite concat_assoc.
    econstructor.
    + apply IHAts.
      * introv Ain. eauto with listin.
      * inversion* Adist.
      * trivial.
    + rewrite dom_concat.
      apply notin_union. constructor.
      * eauto with listin.
      * inversions Adist.
        rewrite add_types_dom_is_from_list.
        apply* fromlist_notin_restated.
Qed.

Lemma typing_weakening : forall Σ E F G e T,
    {Σ, E & G} ⊢ e ∈ T ->
    okt Σ (E & F & G) ->
    {Σ, E & F & G} ⊢ e ∈ T.
Proof.
  introv HTyp. gen F.
  inductions HTyp; introv Ok; eauto.
  - apply* typing_var. apply* binds_weaken.
  - econstructor; eauto.
    introv Tin.
    apply* wft_weaken.
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
  - apply* typing_case.
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
    rewrite add_types_assoc.

    lets IHeq3: IHeq2 E (add_types G Alphas & x ~ bind_var (open_tt_many_var Alphas (Cargtype def))) F.
    + apply JMeq_from_eq.
      rewrite add_types_assoc.
      rewrite concat_assoc. trivial.
    + rewrite concat_assoc in IHeq3.
      apply IHeq3.
      rewrite <- (concat_empty_r G).
      rewrite add_types_assoc.
      rewrite concat_assoc.
      econstructor.
      * apply okt_Alphas_strengthen; trivial.
        introv Ain; lets*: Afresh Ain.
      * match goal with | H: okt Σ ?E |- _ => lets okgadt: okt_implies_okgadt H end.
        unfold okGadt in okgadt.
        destruct okgadt as [okΣ okCtors].
        lets [defsNe okDefs]: okCtors H0.
        lets indef: fst_from_zip Inzip.
        lets okCtor: okDefs indef.
        inversions okCtor.
        cbn.
        rewrite <- add_types_assoc. rewrite concat_empty_r.
        lets*: H5 Alphas (E & F & G).
      * repeat rewrite dom_concat.
        rewrite add_types_dom_is_from_list.
        eauto.
Qed.

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
    + introv inzip. intros Alphas xClause Alen Adist Afresh xfresh xfreshA.
      lets* [i [Hdefs Hmapped]]: Inzip_to_nth_error inzip.
      lets* [[clA' clT'] [Hclin Hclsubst]]: nth_error_map Hmapped.
      destruct clause as [clA clT]. cbn.
      inversions Hclsubst.
      lets* Hzip: Inzip_from_nth_error Hdefs Hclin.
      lets* IH: H4 Hzip.

      assert (Htypfin: {Σ, E & add_types F Alphas & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))}
                ⊢ subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause) ∈ Tc).
      * lets Htmp: IH Alphas xClause Alen Adist Afresh.
        lets Htmp2: Htmp xfresh xfreshA.
        lets Htmp3: Htmp2 E (add_types F Alphas & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))) x U.
        cbn in Htmp3.
        rewrite <- concat_assoc.
        apply* Htmp3.
        apply JMeq_from_eq.
        rewrite add_types_assoc. eauto using concat_assoc.
      * rewrite <- add_types_assoc in Htypfin.
        lets: subst_commutes_open_tt_many.
Admitted.

Hint Resolve okt_subst_tb.


Lemma okt_strengthen_2 : forall Σ E Z P F,
    wft Σ E P ->
    okt Σ (E & (withtyp Z) & F) ->
    okt Σ (E & (EnvOps.map (subst_tb Z P) F)).
  introv WP O. induction F using env_ind.
  - rewrite concat_empty_r in *. lets*: (okt_push_typ_inv O).
    rewrite map_empty.
    rew_env_concat. eauto.
  - rewrite concat_assoc in *.
    lets Hinv: okt_push_inv O; inversions Hinv.
    + lets (?&?): (okt_push_typ_inv O).
      rewrite map_concat.
      rewrite map_single.
      rewrite concat_assoc.
      applys~ okt_sub.
    + match goal with
      | H: exists T, v = bind_var T |- _ =>
        rename H into Hexists_bindvar end.
      inversions Hexists_bindvar.
      lets (?&?&?): (okt_push_var_inv O).
      rewrite map_concat.
      rewrite map_single.
      rewrite concat_assoc.
      applys~ okt_typ.
      applys* wft_subst_tb.
Qed.

Lemma typing_through_subst_te : forall Σ E F Z e T P,
    {Σ, E & (withtyp Z) & F} ⊢ e ∈ T ->
    wft Σ E P ->
    Z \notin fv_typ P -> (* theoretically this assumption should not be needed as it should arise from wft E P /\ okt E + Z (so Z is not in E and P is wft in E so it cannot have free Z), but we can shift this responsibility up *)
    {Σ, E & map (subst_tb Z P) F} ⊢ (subst_te Z P e) ∈ (subst_tt Z P T).
Proof.
  Ltac apply_ih2 :=
    match goal with
    | H: forall X, X \notin ?L -> forall E0 F0 Z0, ?P1 -> ?P2 |- _ =>
      apply_ih_map_bind* H end.
  introv Typ W FP.
  inductions Typ; introv; simpls subst_tt; simpls subst_te; eauto.
  - apply* typing_var. rewrite* (@map_subst_tb_id Σ E Z P).
    match goal with
    | Hbinds: binds _ _ _ |- _ => binds_cases Hbinds; unsimpl_map_bind* end.
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
        apply* wft_subst_tb.
        apply* okt_is_ok.
        apply* okt_strengthen_2.
        lets* reg: typing_regular Typ.
      * apply* subst_commutes_open_tt_many.
        cbn. rewrite* fold_empty.
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
  - (* matchgadt *)
    admit.
Admitted.
