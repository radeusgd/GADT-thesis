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

      assert (Htypfin: {Σ, E & add_types F Alphas & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))}
                ⊢ subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause) ∈ Tc).
      * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
          [ introv Ain; lets*: Afresh Ain | idtac ].
        assert (xfreshL: xClause \notin L); eauto.
        lets Htmp: IH Alphas xClause Alen Adist AfreshL.
        lets Htmp2: Htmp xfreshL xfreshA.
        lets Htmp3: Htmp2 E (add_types F Alphas & xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))) x U.
        cbn in Htmp3.
        rewrite <- concat_assoc.
        apply* Htmp3.
        apply JMeq_from_eq.
        rewrite add_types_assoc. eauto using concat_assoc.
      * rewrite <- add_types_assoc in Htypfin.
        assert (Horder:
                  subst_ee x u (open_te_many_var Alphas clT' open_ee_var xClause)
                  =
                  open_te_many_var Alphas (subst_ee x u clT') open_ee_var xClause).
        -- rewrite* <- subst_ee_open_ee_var.
           f_equal.
           apply* subst_commutes_with_unrelated_opens_te_ee.
        -- rewrite* <- Horder.
Qed.

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
  - eapply typing_case; eauto.
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
      cbn in IH.

      assert (Htypfin: {Σ, add_types (E & map (subst_tb Z P) F) Alphas &
                           xClause ~ bind_var (subst_tt Z P (open_tt_many_var Alphas (Cargtype def)))}
                         ⊢ subst_te Z P (open_te_many_var Alphas clT' open_ee_var xClause)
                         ∈ subst_tt Z P Tc).
      * assert (AfreshL: forall A : var, List.In A Alphas -> A \notin L);
          [ introv Ain; lets*: Afresh Ain | idtac ].
        assert (xfreshL: xClause \notin L); eauto.
        lets Htmp: IH Alphas xClause Alen Adist AfreshL.
        lets Htmp2: Htmp xfreshL xfreshA.
        lets Htmp3: Htmp2 E (add_types F Alphas &
                             xClause ~ bind_var (open_tt_many_var Alphas (Cargtype def))) Z.
        rewrite add_types_assoc.
        rewrite <- concat_assoc.
        rewrite add_types_through_map in Htmp3.
        autorewrite with rew_env_map in Htmp3.
        cbn in Htmp3.
        apply* Htmp3.
        apply JMeq_from_eq.
        rewrite add_types_assoc. eauto using concat_assoc.
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

(* TODO move these to Infrastructure *)
Lemma fv_open_tt : forall x T1 T2 k,
    x \notin fv_typ T1 ->
    x \notin fv_typ T2 ->
    x \notin fv_typ (open_tt_rec k T1 T2).
  introv f1 f2.
  unfold open_tt.
  lets [Ho | Ho]: fv_open T2 T1 k; rewrite Ho; eauto.
Qed.

Lemma fv_open_te : forall e k x T,
    x \notin fv_trm e ->
    x \notin fv_typ T ->
    x \notin fv_trm (open_te_rec k T e).
  induction e using trm_ind'; introv efresh Tfresh;
    try solve [
          cbn in *; eauto
        | cbn in *;
          rewrite notin_union;
          split*; apply* fv_open_tt
        ].
  - cbn. cbn in efresh.
    apply notin_fold.
    + intros T' Tin.
      unfold open_typlist_rec in Tin.
      lets Tin2: Tin.
      apply List.in_map_iff in Tin2.
      destruct Tin2 as [T'' [T'eq T''in]].
      subst.
      apply* fv_open_tt.
    + apply* IHe.
  - cbn in *.
    apply notin_fold.
    + intros cl clin.
      apply List.in_map_iff in clin.
      destruct clin as [[cl'A cl'T] [cl'eq cl'in]].
      subst. cbn.

      rewrite List.Forall_forall in *.
      fold (clauseTerm (clause cl'A cl'T)).
      apply* H.

      cbn.
      fold (clauseTerm (clause cl'A cl'T)).
      apply* fv_fold_in_clause.
    + apply* IHe.
      apply* fv_fold_base_clause.
Qed.

Lemma fv_open_te_many : forall Ts e x,
    (forall T, List.In T Ts -> x \notin fv_typ T) ->
    x \notin fv_trm e ->
    x \notin fv_trm (open_te_many Ts e).
  induction Ts as [| Th Tts]; introv Tfresh efresh.
  - cbn. trivial.
  - cbn. apply IHTts.
    + introv Tin. eauto with listin.
    + unfold open_te.
      apply fv_open_te; eauto with listin.
Qed.

Fixpoint subst_te_many (Xs : list var) (Us : list typ) (e : trm) :=
  match (Xs, Us) with
  (* | ((List.cons X Xt), (List.cons U Ut)) => subst_tt X U (subst_tt_many Xt Ut T) *)
  | ((List.cons X Xt), (List.cons U Ut)) => subst_te_many Xt Ut (subst_te X U e)
  | _ => e
  end.

Lemma subst_commutes_with_unrelated_opens_te : forall Xs e V Y,
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    subst_te Y V (open_te_many_var Xs e) =
    (open_te_many_var Xs (subst_te Y V e)).
  induction Xs as [| Xh Xt]; introv Hneq Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_te_many_var Xt (e open_te_var Xh)).
    fold (open_te_many_var Xt (subst_te Y V e open_te_var Xh)).
    rewrite* subst_te_open_te_var; eauto with listin.
Qed.

Lemma subst_intro_commutes_opens_te : forall Xs e Y V,
    Y \notin fv_trm e ->
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    open_te_many_var Xs (open_te e V) =
    subst_te Y V (open_te_many_var Xs (e open_te_var Y)).
  induction Xs as [| Xh Xt]; introv Hfv Hneq Htyp.
  - cbn. apply* subst_te_intro.
  - cbn.
    fold (open_te_many_var Xt (open_te e V open_te_var Xh)).
    fold (open_te_many_var Xt ((e open_te_var Y) open_te_var Xh)).
    rewrite* subst_commutes_with_unrelated_opens_te.
    f_equal.
    rewrite* <- subst_te_open_te_var.
    + rewrite* <- subst_te_intro.
    + apply* Hneq. cbn; eauto.
    + eauto with listin.
Qed.

Lemma subst_te_intro_many : forall Xs e Us,
    length Xs = length Us ->
    DistinctList Xs ->
    (forall X, List.In X Xs -> X \notin fv_trm e) ->
    (forall X U, List.In X Xs -> List.In U Us -> X \notin fv_typ U) ->
    (forall U, List.In U Us -> type U) ->
    open_te_many Us e = subst_te_many Xs Us (open_te_many_var Xs e).
  induction Xs as [| Xh Xt]; introv Hleneq Hdistinct HXfv HXUfv XUtyp.
  - destruct Us.
    + cbv. trivial.
    + inversions Hleneq.
  - destruct Us as [| Uh Ut].
    + inversions Hleneq.
    + cbn.
      fold (open_te_many_var Xt (e open_te_var Xh)).
      inversions Hdistinct.
      rewrite IHXt; auto with listin.
      * f_equal.
        rewrite <- subst_intro_commutes_opens_te; eauto with listin.
        introv Xin.
        intro; subst. contradiction.
      * introv Xin.
        apply fv_open_te; eauto with listin.
Qed.

Lemma open_tt_many_closed : forall As T,
    type T ->
    open_tt_many As T = T.
  induction As; introv Hcl.
  - cbn. trivial.
  - cbn. unfold open_tt.
    rewrite* <- open_tt_rec_type.
Qed.

Lemma subst_tt_many_free : forall As Ts T,
    (forall A, List.In A As -> A \notin fv_typ T) ->
    T = subst_tt_many As Ts T.
  induction As; introv Afresh.
  - cbn. trivial.
  - destruct Ts.
    + cbn. trivial.
    + cbn. rewrite <- IHAs.
      * symmetry. apply subst_tt_fresh.
        auto with listin.
      * intros.
        rewrite subst_tt_fresh;
          auto with listin.
Qed.

Lemma subst_te_many_commutes_open : forall As Ts e x,
    length As = length Ts ->
    (forall A, List.In A As -> x <> A) ->
    (subst_te_many As Ts e) open_ee_var x
    =
    subst_te_many As Ts (e open_ee_var x).
  induction As as [| Ah Ats]; introv Hlen Afresh.
  - cbn. auto.
  - destruct Ts as [| Th Tts]; cbn in Hlen; try congruence.
    cbn. fold (open_ee (subst_te_many Ats Tts (subst_te Ah Th e)) (trm_fvar x)).
    rewrite IHAts; auto with listin.
    f_equal.
    apply subst_te_open_ee_var.
Qed.

Definition subst_tb_many (As : list var) (Ps : list typ) (b : bind) : bind :=
  match b with
  | bind_typ => bind_typ
  | bind_var T => bind_var (subst_tt_many As Ps T)
  end.

Lemma env_map_ext_id : forall T (E : env T) (f : T -> T),
    (forall x, f x = x) ->
    map f E = E.
  induction E using env_ind; introv fext;
    autorewrite with rew_env_map; trivial.
  - rewrite* IHE.
    rewrite fext.
    trivial.
Qed.

Lemma env_map_compose : forall A B C (E : env A) (f : A -> B) (g : B -> C) (h : A -> C),
    (forall x, g (f x) = h x) ->
    map g (map f E) = map h E.
  induction E using env_ind; introv Hcomp;
    autorewrite with rew_env_map; trivial.
  - lets IH: IHE f g h.
    rewrite IH; auto.
    rewrite Hcomp. trivial.
Qed.

Lemma typing_through_subst_te_many : forall As Σ E F e T Ps,
    {Σ, E & (add_types empty As) & F} ⊢ e ∈ T ->
    length As = length Ps ->
    (forall P, List.In P Ps -> wft Σ E P) ->
    (forall A, List.In A As -> A # E) ->
    (forall A, List.In A As -> A # F) ->
    (forall A P, List.In A As -> List.In P Ps -> A \notin fv_typ P) ->
    DistinctList As ->
    (* Z \notin fv_typ P -> (* theoretically this assumption should not be needed as it should arise from wft E P /\ okt E + Z (so Z is not in E and P is wft in E so it cannot have free Z), but we can shift this responsibility up *) *)
    (* CT = (subst_tt_many As Ts T) -> *)
    {Σ, E & map (subst_tb_many As Ps) F} ⊢ (subst_te_many As Ps e) ∈  subst_tt_many As Ps T.
  (* TODO the thm statement needs some fixes *)
  induction As as [| Ah Ats]; introv Htyp Hlen Pwft AE AF AP Adist.
  - cbn. unfold subst_tb_many. cbn.
    rewrite env_map_ext_id;
      [ idtac | intro xb; destruct xb; cbn; trivial ].
    cbn in Htyp. rewrite concat_empty_r in Htyp. trivial.
  - destruct Ps as [| Ph Pts]; cbn in Hlen; try congruence.
    cbn.
    lets Hcomp: env_map_compose (subst_tb Ah Ph) (subst_tb_many Ats Pts).
    rewrite <- Hcomp;
      [ idtac
      | intros bd; destruct bd; cbn; trivial ].
    apply IHAts; eauto with listin.
    apply typing_through_subst_te.
    + cbn in Htyp. autorewrite with rew_env_concat in Htyp. trivial.
    + assert (HWFT: wft Σ E Ph); eauto with listin.
      rewrite <- add_types_assoc.
      rewrite concat_empty_r.
      expand_env_empty (add_types E Ats).
      apply wft_weaken_many; autorewrite with rew_env_concat; eauto with listin.
      * lets [Hokt]: typing_regular Htyp.
        apply okt_strengthen_simple in Hokt.
        apply okt_strengthen_simple in Hokt.
        apply* okt_is_ok.
      * inversion* Adist.
    + eauto with listin.
    + inversion* Adist.
Qed.

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

    (* we reduce to one of the branches which correspond to their definitions in type *)
    lets* [Def [nthDef Inzip]]: nth_error_implies_zip_swap Defs H10.
    lets HclTyp: H3 Inzip.
    remember (Cargtype Def) as argT.

    (* prepare fresh vars *)
    let fresh := gather_vars in
    lets* [Alphas [Hlen [Adist Afresh]]]: exist_alphas fresh (length Ts0).
    rewrite length_equality in Hlen.
    pick_fresh x.

    inversions H7.

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
Qed.

