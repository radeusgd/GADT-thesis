Set Implicit Arguments.
Require Import Prelude.
Require Import Infrastructure.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.


Ltac fold_delta :=
  repeat match goal with
  | [ H: context [List.map tc_var ?As] |- _ ] =>
    fold (tc_vars As) in H
  | [ H: context [ (tc_var ?X) :: ?As] |- _ ] =>
    match As with
    | [] => fail 1
    | _ => fold ([tc_var X] ++ As) in H
    end
  | [ |- context [List.map tc_var ?As] ] =>
    fold (tc_vars As)
  | [ |- context [ (tc_var ?X) :: ?As] ] =>
    match As with
    | [] => fail 1
    | _ => fold ([tc_var X] ++ As)
    end
  end.

Ltac destruct_in_app :=
  match goal with
  | [ H: List.In ?X (?A ++ ?B) |- _ ] =>
    apply List.in_app_or in H;
    destruct H
  | [ H: is_var_defined (?A ++ ?B) ?X |- _ ] =>
    unfold is_var_defined in H;
    apply List.in_app_or in H;
    destruct H
  end.

(** * Regularity *)
(**
Defines basic properties of well formed types and typing judgement.
*)

(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma type_from_wft : forall Σ E T,
  wft Σ E T -> type T.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve type_from_wft.

Lemma values_decidable : forall t,
    term t ->
    (value t \/ ~ (value t)).
  induction t; intro H;
  inversion H; subst; try solve [
                     right; intro Hv; inversion Hv
                   | left; econstructor
                          ].
  - match goal with
    | H: term t |- _ => rename H into Ht end.
    apply IHt in Ht.
    destruct Ht as [Hv | Hv].
    + left; constructor*.
    + right. intro Hv'. inversion* Hv'.
  - match goal with
    | H: term t1 |- _ => rename H into Ht1 end.
    match goal with
    | H: term t2 |- _ => rename H into Ht2 end.
    apply IHt1 in Ht1.
    apply IHt2 in Ht2.
    destruct Ht1;
      destruct Ht2;
      try solve [ left; econstructor; eauto
                | right; intro Hv; inversion Hv; congruence ].
  - left; econstructor.
    econstructor; eauto.
  - left; econstructor.
    econstructor; eauto.
Qed.

Ltac IHap IH := eapply IH; eauto;
                try (unfold open_ee; rewrite <- open_ee_var_preserves_size);
                try (unfold open_te; rewrite <- open_te_var_preserves_size);
                cbn; lia.

(* Lemma wft_weaken : forall Σ Δ E F G T, *)
(*     wft Σ Δ (E & G) T -> *)
(*     ok (E & F & G) -> *)
(*     wft Σ Δ (E & F & G) T. *)
(*   introv Hwft Hok. gen_eq K: (E & G). gen E F G. *)
(*   induction Hwft; intros; subst; auto. *)
(*   - (* case: var *) *)
(*     apply (@wft_var Σ (E0 & F & G) X).  apply* binds_weaken. *)
(*   - (* case: all *) *)
(*     apply_fresh* wft_all as X. apply_ih_bind* H0. *)
(*   - econstructor; eauto. *)
(* Qed. *)

Hint Resolve subst_tt_type subst_te_term subst_ee_term.
Hint Resolve subst_te_value subst_ee_value.

Lemma okt_is_ok : forall Σ Δ E, okt Σ Δ E -> ok E.
  introv. intro Hokt.
  induction Hokt; eauto.
Qed.
Hint Extern 1 (ok _) => apply okt_is_ok.


Lemma wft_from_env_has_typ : forall Σ Δ x U E,
    okt Σ Δ E -> binds x (bind_var U) E -> wft Σ Δ U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
  - false (empty_push_inv H).
  - destruct (eq_push_inv H) as [? [? ?]]; subst. clear H.
    lets [[? HT] | [? HB]]: binds_push_inv B.
    + inversion* HT.
    + apply* IHE.
  (* - destruct (eq_push_inv H) as [? [? ?]]; subst. clear H. *)
  (*   destruct (binds_push_inv B) as [[? ?]|[? ?]]; subst. *)
  (*   + admit. *)
  (*   + expand_env_empty (E & x0 ~ bind_typ); apply* wft_weaken; fold_env_empty. *)
  (*     econstructor. apply* okt_is_ok. auto. *)
  (* - destruct (eq_push_inv H) as [? [? ?]]. clear H. *)
  (*   destruct (binds_push_inv B) as [[? Hbindeq]|[? Hbinds]]; subst. *)
  (*   + inversions Hbindeq. *)
  (*     expand_env_empty (E & x0 ~ bind_var T); apply* wft_weaken; fold_env_empty. *)
  (*     econstructor. apply* okt_is_ok. auto. *)
  (*   + inversions Hbinds. *)
  (*     expand_env_empty (E & x0 ~ bind_var T); apply* wft_weaken; fold_env_empty. *)
  (*     constructor*. *)
  (*     apply* okt_is_ok. *)
Qed.

Lemma wft_strengthen_typ : forall Σ D1 D2 U T,
    U \notin fv_typ T ->
    wft Σ (D1 |,| [tc_var U] |,| D2) T -> wft Σ (D1 |,| D2) T.
Proof.
  introv Ufresh Hwft. gen_eq G: (D1 |,| [tc_var U] |,| D2). gen D2.
  induction Hwft; intros F EQ; cbn in Ufresh; subst; auto.
  - apply* wft_var.
    repeat destruct_in_app;
      unfold is_var_defined; eauto using List.in_or_app.
    cbn in H. intuition. inversions H0. exfalso; eauto using in_singleton_self.
  - (* todo: binds_cases tactic *)
    match goal with
    | H: forall X, X \notin L -> ?P3 -> forall F0, ?P1 -> ?P2 |- _ =>
      rename H into H_ctxEq_implies_wft end.
    apply_fresh* wft_all as Y.
    lets* IH: H_ctxEq_implies_wft Y (F |,| [tc_var Y]).
    + lets [Hfv | Hfv]: fv_open T2 (typ_fvar Y) 0;
        cbn in Hfv; unfold open_tt; rewrite Hfv; eauto.
    + rewrite <- List.app_assoc.
      apply IH. eauto using List.app_assoc.
  - econstructor; eauto.
Qed.

Lemma wft_strengthen_typ_many : forall Σ As Δ T,
    wft Σ (Δ |,| tc_vars As) T ->
    (forall A, List.In A As -> A \notin fv_typ T) ->
    wft Σ Δ T.
  induction As as [| Ah Ats]; introv Hwft Asfresh.
  - cbn in *. clean_empty_Δ.
    trivial.
  - cbn in *. fold_delta. fold_delta.
    apply* IHAts.
    apply* wft_strengthen_typ.
    rewrite* <- List.app_assoc.
Qed.
(* Lemma wft_strengthen : forall Σ Δ E F x U T, *)
(*  wft Σ Δ (E & (x ~: U) & F) T -> wft Σ (E & F) T. *)
(* Proof. *)
(*   introv Hwft. gen_eq G: (E & (x ~: U) & F). gen F. *)
(*   induction Hwft; intros F EQ; subst; auto. *)
(*   - *)
(*     match goal with *)
(*     | H: binds _ _ _ |- _ => *)
(*       rename H into Hbinds_bindtyp end. *)
(*     apply* (@wft_var). *)
(*     destruct (binds_concat_inv Hbinds_bindtyp) as [?|[? Hbinds2]]. *)
(*     + apply~ binds_concat_right. *)
(*     + destruct (binds_push_inv Hbinds2) as [[? ?]|[? ?]]. *)
(*       * subst. false. *)
(*       * apply~ binds_concat_left. *)
(*   - (* todo: binds_cases tactic *) *)
(*     match goal with *)
(*     | H: forall X, X \notin L -> forall F0, ?P1 -> ?P2 |- _ => *)
(*       rename H into H_ctxEq_implies_wft end. *)
(*     apply_fresh* wft_all as Y. apply_ih_bind* H_ctxEq_implies_wft. *)
(*   - econstructor; eauto. *)
(* Qed. *)

Lemma okt_implies_okgadt : forall Σ Δ E, okt Σ Δ E -> okGadt Σ.
  induction 1; auto.
Qed.

Ltac find_ctxeq :=
  match goal with
  | H: _ & _ ~ _ = _ & _ ~ _ |- _ =>
    rename H into Hctx_eq
  end.

Lemma okt_push_var_inv : forall Σ Δ E x T,
  okt Σ Δ (E & x ~: T) -> okt Σ Δ E /\ wft Σ Δ T /\ x # E.
Proof.
  introv O; inverts O.
  - false* empty_push_inv.
  - find_ctxeq. lets (?&M&?): (eq_push_inv Hctx_eq). subst. inverts~ M.
Qed.

Lemma okt_is_wft : forall Σ Δ E x T,
    okt Σ Δ (E & x ~: T) -> wft Σ Δ T.
  introv Hokt.
  inversion Hokt.
  - false* empty_push_inv.
  (* - lets (?&?&?): eq_push_inv H. false*. *)
  - lets (?&?&?): eq_push_inv H. subst.
    match goal with Heq: bind_var ?T1 = bind_var ?T2 |- _ => inversions* Heq end.
Qed.

Lemma okt_strengthen : forall Σ Δ E x U F,
    okt Σ Δ (E & (x ~: U) & F) -> okt Σ Δ (E & F).
  introv O. induction F using env_ind.
  - rewrite concat_empty_r in *. lets*: (okt_push_var_inv O).
  - rewrite concat_assoc in *.
    (* lets Hinv: okt_push_inv O; inversions Hinv. *)
    (* + lets (?&?): (okt_push_typ_inv O). *)
    (*   applys~ okt_sub. *)
    (* + match goal with *)
    (*   | H: exists T, v = bind_var T |- _ => *)
    (*     rename H into Hexists_bindvar end. *)
      (* inversions Hexists_bindvar. *)
    (* lets (?&?&?): (okt_push_var_inv O). *)
    destruct v.
    inversions O.
    + false* empty_push_inv.
    + apply eq_push_inv in H.
      destruct H as [? [? ?]]. subst.
      match goal with
      | [ H: bind_var ?T = bind_var ?t |- _ ] => inversions H
      end.
      applys~ okt_typ.
Qed.

Lemma okt_strengthen_delta_var : forall Σ D1 D2 E X,
    X # E ->
    X \notin fv_env E ->
    okt Σ (D1 |,| [tc_var X] |,| D2) E -> okt Σ (D1 |,| D2) E.
  introv FXE FXTE O. induction E using env_ind.
  - constructor.
    lets*: okt_implies_okgadt.
  - destruct v as [T].
    inversions O.
    + lets*: empty_push_inv H.
    + lets [? [? ?]]: eq_push_inv H.
      match goal with
      | H: bind_var ?A = bind_var ?B |- _ => inversions H
      end.
      lets [? ?]: notin_env_inv FXTE.
      constructor; auto.
      * apply wft_strengthen_typ with X; auto.
      * apply notin_domΔ_eq.
        apply notin_domΔ_eq in H5.
        destruct H5.
        apply notin_domΔ_eq in H5.
        intuition.
Qed.

Lemma okt_is_type : forall Σ Δ E x T,
    okt Σ Δ (E & x ~: T) -> type T.
  introv Hokt. apply okt_is_wft in Hokt. apply* type_from_wft.
Qed.

(* Ltac unsimpl_map_bind_typ Z P := *)
(*   match goal with *)
(*   | |- context [ bind_typ ] => *)
(*     unsimpl (subst_tb Z P bind_typ) *)
(*   end. *)

Lemma wft_type : forall Σ Δ T,
    wft Σ Δ T -> type T.
Proof.
  induction 1; eauto.
Qed.

Lemma wft_weaken : forall Σ D1 D2 D3 T,
    wft Σ (D1 |,| D3) T ->
    wft Σ (D1 |,| D2 |,| D3) T.
  introv WT. gen_eq K: (D1 |,| D3). gen D3.
  induction WT; auto; introv EQ.
  - constructor. unfold is_var_defined in *.
    subst.
    lets [? | ?]: List.in_app_or H;
      auto using List.in_or_app.
  - apply_fresh* wft_all as Y.
    assert (Yfr: Y \notin L); eauto.
    lets: H0 Yfr (D3 |,| [tc_var Y]).
    assert (Hassoc: ((D1 |,| D2) |,| (D3 |,| [tc_var Y])) = (((D1 |,| D2) |,| D3) |,| [tc_var Y]));
      auto using List.app_assoc.
    rewrite <- Hassoc.
    apply H1. subst. auto using List.app_assoc.
  - apply* wft_gadt.
Qed.

Ltac destruct_app_list :=
  match goal with
  | [ H: List.In ?X (?L ++ ?K) |- _ ] =>
    apply List.in_app_or in H; destruct H
  end.

Lemma wft_subst_tb : forall Σ D1 D2 Z P T,
  wft Σ (D1 |,| [tc_var Z] |,| D2) T ->
  wft Σ D1 P ->
  wft Σ (D1 |,| D2) (subst_tt Z P T).
Proof.
  introv WT WP; gen_eq G: (D1 |,| [tc_var Z] |,| D2). gen D2.
  induction WT; intros; subst; simpl subst_tt; auto.
  - case_var*.
    + lets Hw: wft_weaken D1 D2 emptyΔ.
      repeat rewrite List.app_nil_r in *.
      apply* Hw.
    + constructor. unfold is_var_defined in *.
      repeat destruct_app_list; auto using List.in_or_app.
      cbn in H. destruct H.
      * congruence.
      * contradiction.
  - apply_fresh* wft_all as Y.
    lets: wft_type.
    rewrite* subst_tt_open_tt_var.
    lets* IH: H0 Y (D2 |,| [tc_var Y]).
    rewrite <- List.app_assoc.
    apply IH. auto using List.app_assoc.
  - apply* wft_gadt.
    + introv Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [U [? Tin]]; subst.
      apply* H0.
    + apply List.map_length.
Qed.

(* Lemma wft_subst_tb : forall Σ F E Z P T, *)
(*   wft Σ (E & (withtyp Z) & F) T -> *)
(*   wft Σ E P -> *)
(*   ok (E & map (subst_tb Z P) F) -> *)
(*   wft Σ (E & map (subst_tb Z P) F) (subst_tt Z P T). *)
(* Proof. *)
(*   introv WT WP. gen_eq G: (E & (withtyp Z) & F). gen F. *)
(*   induction WT as [ | | | | ? ? ? ? ? IH | ]; intros F EQ Ok; subst; simpl subst_tt; auto. *)
(*   - case_var*. *)
(*     + expand_env_empty (E & map (subst_tb Z P) F). *)
(*       apply* wft_weaken; fold_env_empty. *)
(*     + destruct (binds_concat_inv H) as [?|[? ?]]. *)
(*       * apply wft_var. *)
(*         apply~ binds_concat_right. *)
(*         unsimpl_map_bind_typ Z P. *)
(*         apply~ binds_map. *)
(*       * destruct (binds_push_inv H1) as [[? ?]|[? ?]]. *)
(*         -- subst. false~. *)
(*         -- applys wft_var. apply* binds_concat_left. *)
(*   - apply_fresh* wft_all as Y. *)
(*     unsimpl ((subst_tb Z P) bind_typ). *)
(*     lets: wft_type. *)
(*     rewrite* subst_tt_open_tt_var. *)
(*     apply_ih_map_bind* IH. *)
(*   - econstructor; eauto. *)
(*     + introv Tin. *)
(*       apply List.in_map_iff in Tin. *)
(*       destruct Tin as [T' Tand]. *)
(*       destruct Tand as [Teq Tin]. *)
(*       rewrite <- Teq. *)
(*       apply* H0. *)
(*     + apply List.map_length. *)
(* Qed. *)
(* Hint Resolve wft_subst_tb. *)

Lemma wft_open : forall Σ Δ U T1,
  wft Σ Δ (typ_all T1) ->
  wft Σ Δ U ->
  wft Σ Δ (open_tt T1 U).
Proof.
  introv WA WU. inversions WA. pick_fresh X.
  rewrite* (@subst_tt_intro X).
  lets K: (@wft_subst_tb Σ Δ emptyΔ X).
  clean_empty_Δ.
  apply* K.
Qed.

(** ** GADT environment properties *)

Hint Resolve okt_is_ok.

Lemma gadt_constructor_ok : forall Σ Name Tarity Ctors Ctor Carity CargType CretTypes,
    binds Name (mkGADT Tarity Ctors) Σ ->
    List.nth_error Ctors Ctor = Some (mkGADTconstructor Carity CargType CretTypes) ->
    okGadt Σ ->
    okConstructorDef Σ Tarity (mkGADTconstructor Carity CargType CretTypes).
  introv Hbind Hlist HokG.
  inversion HokG as [Hok HokG'].
  apply* HokG'.
  apply* List.nth_error_In.
Qed.

(* Lemma wft_open_gadt : forall , *)
(*   forall T : typ, List.In T Ts -> wft Σ E T *)
(*   Hokt : okt Σ E *)
(*   Hterm : term e1 *)
(*   Hwft : wft Σ E (open_tt_many CargType Ts) *)
(*   HG : okGadt Σ *)
(*        wft Σ (add_types empty Alphas) (open_tt_many_var retT Alphas) -> *)
(*   wft Σ E (open_tt_many (typ_gadt CretTypes Name) Ts) *)

(** ** More WFT Properties *)

(* Most likely not needed anymore as wft_weaken already supports arbitrary middle *)
(* Lemma wft_weaken_many : forall Σ As D1 D2 T, *)
(*     wft Σ (D1 |,| D2) T -> *)
(*     (forall A, List.In A As -> A \notin domΔ D1) -> *)
(*     (forall A, List.In A As -> A \notin domΔ D2) -> *)
(*     DistinctList As -> *)
(*     wft Σ (D1 |,| tc_vars As |,| D2) T. *)
(*   induction As as [| Ah Ats]; introv Hwft FD1 FD2 Hdist. *)
(*   - cbn. clean_empty_Δ. auto. *)
(*   - cbn. fold (tc_vars Ats). *)
(*     fold_delta. *)
(*     apply wft_weaken. *)
(*     rewrite <- concat_assoc. *)
(*     apply* IHAs; try eauto with listin. *)
(*     + rewrite concat_assoc. *)
(*       eapply adding_free_is_ok; eauto with listin. *)
(*     + rewrite concat_assoc. *)
(*       apply* wft_weaken. *)
(*       eapply adding_free_is_ok; eauto with listin. *)
(*     + introv Hin. *)
(*       simpl_dom. *)
(*       rewrite notin_union. *)
(*       split. *)
(*       * apply* notin_singleton. *)
(*         inversions HAs. *)
(*         intro; subst. contradiction. *)
(*       * eauto with listin. *)
(*     + inversion* HAs. *)
(* Qed. *)

Lemma wft_subst_tb_many : forall Σ (As : list var) (Us : list typ) Δ (T : typ),
    length As = length Us ->
      wft Σ (Δ |,| tc_vars As) T ->
      (forall U, List.In U Us -> wft Σ Δ U) ->
      (* (forall A, List.In A As -> A \notin dom E) -> *)
      DistinctList As ->
      wft Σ Δ (subst_tt_many As Us T).
  induction As as [|Ah Ats];
    introv Hlen HwftT WwftUs HD;
    destruct Us as [|Uh Uts]; inversion Hlen.
  - cbn in *.
    clean_empty_Δ.
    auto.
  - cbn in *. inversions HD.
    apply IHAts; eauto with listin.
    fold (tc_vars Ats) in HwftT.
    fold ([tc_var Ah] ++ tc_vars Ats) in HwftT.
    apply* wft_subst_tb.
    rewrite* List.app_assoc in HwftT.
Qed.

Lemma wft_open_many : forall Δ Σ Alphas Ts U,
    length Alphas = length Ts ->
    DistinctList Alphas ->
    (* (forall A : var, List.In A Alphas -> A \notin dom E) -> *)
    (forall A : var, List.In A Alphas -> A \notin fv_typ U) ->
    (forall (A : var) (T : typ), List.In A Alphas -> List.In T Ts -> A \notin fv_typ T) ->
    (forall T : typ, List.In T Ts -> wft Σ Δ T) ->
    wft Σ (Δ |,| tc_vars Alphas) (open_tt_many_var Alphas U) ->
    wft Σ Δ (open_tt_many Ts U).
  introv Hlen Hdistinct FU FT WT WU.
  rewrite* (@subst_tt_intro_many Alphas).
  - lets Htb: (@wft_subst_tb_many Σ Alphas Ts).
    specializes_vars Htb.
    apply* Htb.
Qed.

Hint Rewrite in_union : fsets.

Lemma notin_fv_wf : forall Σ Δ X T,
    wft Σ Δ T -> (~ is_var_defined Δ X) -> X \notin fv_typ T.
Proof.
  induction 1 as [ | ? ? ? Hbinds | | | |];
    introv Fr; simpl; eauto.
  - rewrite notin_singleton. intro. subst. contradiction.
  - notin_simpl; auto. pick_fresh Y. apply* (@notin_fv_tt_open Y).
    apply* H0.
    intro HF.
    destruct_in_app.
    + contradiction.
    + cbn in H1. destruct H1; try contradiction.
      apply Fr0. inversions H1.
      autorewrite with fsets. eauto using in_singleton_self.
  - intro Hin.
    lets* Hex: in_fold_exists Hin.
    destruct Hex as [Hex | Hex].
    + destruct Hex as [T [Tin fvT]].
      lets* Hf: H0 T Tin.
    + apply* in_empty_inv.
Qed.

Lemma typing_regular : forall Σ Δ E e T,
   {Σ, Δ, E} ⊢ e ∈ T -> okt Σ Δ E /\ term e /\ wft Σ Δ T.
Proof.
  induction 1 as [ |
                   |
                   | ? ? ? ? ? ? ? ? IH
                   |
                   | ? ? ? ? ? ? ? ? IH
                   | | | |
                   | ? ? ? ? ? ? IHval ? IH
                   | ? ? ? ? ? ? ? ? ? ? ? IH
                   |
                   ];
    try solve [splits*].
  - splits*. apply* wft_from_env_has_typ.
  - subst. destruct IHtyping as [Hokt [Hterm Hwft]].
    subst.
    splits*.
    lets* HG: okt_implies_okgadt Hokt.
    lets* GADTC: gadt_constructor_ok HG.
    inversions GADTC.
    rewrite rewrite_open_tt_many_gadt.
    econstructor; eauto.
    + introv TiL.
      lets* TiL2: TiL. apply List.in_map_iff in TiL2.
      inversion TiL2 as [CretT [Heq CiC]]. subst.
      let usedvars := gather_vars in
      lets* EAlphas: exist_alphas (usedvars) (length Ts).
      inversion EAlphas as [Alphas [A1 [A2 A3]]].
      rewrite length_equality in A1.
      lets* HH: H10 Alphas CiC.
      apply (@wft_open_many Δ Σ Alphas Ts); eauto;
        intros A; lets* FA: A3 A.
      introv Ain Tin.
      apply* fv_typs_notin.
    + rewrite List.map_length. trivial.
  - pick_fresh y.
    copyTo IH IH1.
    assert (yL: y \notin L); eauto.
    lets [? [? ?]]: IH yL.
    (* forwards* Hctx: okt_push_inv. *)
    (* destruct Hctx as [? | Hctx]; try congruence. *)
    (* destruct Hctx as [U HU]. inversions HU. *)
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor.
      * apply* okt_is_type.
      * intros.  apply* IH1.
    + econstructor; eauto.
      apply* okt_is_wft.
  - splits*.
    destruct IHtyping2 as [? [? Hwft]]. inversion* Hwft.
  - copyTo IH IH1.
    pick_fresh_gen (L \u fv_env E \u dom E) y.
    add_notin y L. lets HF: IH1 Fr0. destructs~ HF.
    splits*.
    + rewrite <- (List.app_nil_r Δ).
      apply okt_strengthen_delta_var with y; eauto.
      clean_empty_Δ. auto.
    + apply* term_tabs. intros. apply* IH1.
    + apply_fresh* wft_all as Y.
      add_notin Y L. lets HF: IH1 Y Fr1. destruct* HF.
  - subst. splits*. destruct IHtyping as [? [? Hwft]].
    copyTo Hwft Hwft2.
    inversions Hwft.
    match goal with
    | IH: forall X : var, X \notin L -> ?conclusion |- _ =>
      pick_fresh Y; add_notin Y L; lets HW: IH Y Fr0
    end.
    apply* wft_open.
  - splits*.
    destruct IHtyping as [? [? Hwft]]. inversion* Hwft.
  - splits*.
    destruct IHtyping as [? [? Hwft]]. inversion* Hwft.
  - pick_fresh y.
    copyTo IH IH1.
    specializes IH1 y. destructs~ IH1.
    (* destruct hp as [? | hex]; try congruence. *)
    (* destruct hex as [u hu]. inversions hu. *)
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor. apply* okt_is_type.
      intros. apply* IH.
      intros. apply* IHval.
  - destructs IHtyping.
    pick_fresh y.
    copyTo IH IH1.
    specializes IH y. destructs~ IH.
    (* forwards* Hctx: okt_push_inv. *)
    (* destruct Hctx as [? | Hctx]; try congruence. *)
    (* destruct Hctx as [U HU]. inversions HU. *)
    splits*.
    + econstructor. auto.
      introv HxiL. lets HF: IH1 x HxiL. destruct* HF.
  - destruct IHtyping as [Hokt [Hterme HwftT]].
    splits*.
    + econstructor; eauto.
      intros cl clin Alphas x Hlen Hdist Afresh xfresh.
      destruct cl as [clA clT].
      cbn.
      apply F2_from_zip in H5; eauto.
      lets* [Def [DefIn [DefIn2 HDef]]]: forall2_from_snd clin.
      cbn in HDef.
      cbn in Hlen.
      lets Hlen2: H3 DefIn2.
      cbn in Hlen2.
      assert (Hlen3: length Alphas = Carity Def); try lia.
      lets* HF: HDef Alphas x Hlen3 Hdist Afresh.
    + assert (ms <> []).
      * lets gadtOk: okt_implies_okgadt Hokt.
        inversion gadtOk as [? okDefs].
        lets [defNEmpty okDef]: okDefs H1.
        intro.
        destruct Defs; subst; eauto. cbn in H2. lia.
      * destruct ms as [ | cl1 rest]; [ contradiction | idtac ].
        apply F2_from_zip in H5; eauto.
        lets* [Def [DefIn [DefIn2 HDef]]]: forall2_from_snd cl1 H5;
          eauto with listin.

        (* May want a tactic 'pick_fresh Alphas' *)
        lets* [Alphas [A1 [A2 A3]]]: exist_alphas (Carity Def).
        rewrite length_equality in A1.
        instantiate (1:=L \u fv_typ Tc) in A3.
        pick_fresh x.

        assert (Afresh: (forall A : var, List.In A Alphas -> A \notin L));
          [ introv Ain; lets*: A3 Ain | idtac ].
        assert (xfresh: x \notin L); eauto.

        lets* [? [? Hwft2]]: HDef A1 A2 Afresh xfresh.
        apply wft_strengthen_typ_many with Alphas; auto.
        -- introv Ain. lets*: A3 Ain.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; autos*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

(* does not seem to be helpful for proving safety, just a useful result on its own, but let's ignore it while there are more pressing theorems to prove *)
(* Lemma red_regular : forall t t', *)
(*   red t t' -> term t /\ term t'. *)
(* Proof. *)
(*   induction 1; split; autos* value_regular. *)
(*   - inversions H. pick_fresh y. rewrite* (@subst_ee_intro y). *)
(*   - inversions H. pick_fresh Y. rewrite* (@subst_te_intro Y). *)
(*   - inversions H. pick_fresh y. rewrite* (@subst_ee_intro y). *)
(*   - inversions H. auto. *)
(*   - inversions H. auto. *)
(*   - inversions IHred. econstructor. *)
(* Qed. *)


Lemma typing_implies_term : forall Σ Δ E e T,
    {Σ, Δ, E} ⊢ e ∈ T ->
    term e.
  intros.
  lets TR: typing_regular Σ E e T.
  destruct* TR.
Qed.
