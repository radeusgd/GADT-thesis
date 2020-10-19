Set Implicit Arguments.
Require Import Prelude.
Require Import Infrastructure.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.

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

Lemma wft_weaken : forall Σ E F G T,
    wft Σ (E & G) T ->
    ok (E & F & G) ->
    wft Σ (E & F & G) T.
  introv Hwft Hok. gen_eq K: (E & G). gen E F G.
  induction Hwft; intros; subst; auto.
  - (* case: var *)
    apply (@wft_var Σ (E0 & F & G) X).  apply* binds_weaken.
  - (* case: all *)
    apply_fresh* wft_all as X. apply_ih_bind* H0.
  - econstructor; eauto.
Qed.

Hint Resolve subst_tt_type subst_te_term subst_ee_term.
Hint Resolve subst_te_value subst_ee_value.

Lemma okt_is_ok : forall Σ E, okt Σ E -> ok E.
  introv. intro Hokt.
  induction Hokt; eauto.
Qed.
Hint Extern 1 (ok _) => apply okt_is_ok.

Lemma wft_from_env_has_typ : forall Σ x U E,
    okt Σ E -> binds x (bind_var U) E -> wft Σ E U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
  - false (empty_push_inv H).
  - destruct (eq_push_inv H) as [? [? ?]]; subst. clear H.
    destruct (binds_push_inv B) as [[? ?]|[? ?]]; subst.
    + inversions H1.
    + expand_env_empty (E & x0 ~ bind_typ); apply* wft_weaken; fold_env_empty.
      econstructor. apply* okt_is_ok. auto.
  - destruct (eq_push_inv H) as [? [? ?]]. clear H.
    destruct (binds_push_inv B) as [[? Hbindeq]|[? Hbinds]]; subst.
    + inversions Hbindeq.
      expand_env_empty (E & x0 ~ bind_var T); apply* wft_weaken; fold_env_empty.
      econstructor. apply* okt_is_ok. auto.
    + inversions Hbinds.
      expand_env_empty (E & x0 ~ bind_var T); apply* wft_weaken; fold_env_empty.
      constructor*.
      apply* okt_is_ok.
Qed.

Lemma wft_strengthen : forall Σ E F x U T,
 wft Σ (E & (x ~: U) & F) T -> wft Σ (E & F) T.
Proof.
  introv Hwft. gen_eq G: (E & (x ~: U) & F). gen F.
  induction Hwft; intros F EQ; subst; auto.
  -
    match goal with
    | H: binds _ _ _ |- _ =>
      rename H into Hbinds_bindtyp end.
    apply* (@wft_var).
    destruct (binds_concat_inv Hbinds_bindtyp) as [?|[? Hbinds2]].
    + apply~ binds_concat_right.
    + destruct (binds_push_inv Hbinds2) as [[? ?]|[? ?]].
      * subst. false.
      * apply~ binds_concat_left.
  - (* todo: binds_cases tactic *)
    match goal with
    | H: forall X, X \notin L -> forall F0, ?P1 -> ?P2 |- _ =>
      rename H into H_ctxEq_implies_wft end.
    apply_fresh* wft_all as Y. apply_ih_bind* H_ctxEq_implies_wft.
  - econstructor; eauto.
Qed.

Lemma okt_implies_okgadt : forall Σ E, okt Σ E -> okGadt Σ.
  induction 1; auto.
Qed.

Ltac find_ctxeq :=
  match goal with
  | H: _ & _ ~ _ = _ & _ ~ _ |- _ =>
    rename H into Hctx_eq
  end.

Lemma okt_push_var_inv : forall Σ E x T,
  okt Σ (E & x ~: T) -> okt Σ E /\ wft Σ E T /\ x # E.
Proof.
  introv O; inverts O.
  - false* empty_push_inv.
  - find_ctxeq. lets (?&?&?): (eq_push_inv Hctx_eq). false.
  - find_ctxeq. lets (?&M&?): (eq_push_inv Hctx_eq). subst. inverts~ M.
Qed.

Lemma okt_push_typ_inv : forall Σ E X,
  okt Σ (E & withtyp X) -> okt Σ E /\ X # E.
Proof.
  introv O. inverts O.
  - false* empty_push_inv.
  - find_ctxeq. lets (?&M&?): (eq_push_inv Hctx_eq). subst. inverts~ M.
  - find_ctxeq. lets (?&?&?): (eq_push_inv Hctx_eq). false.
Qed.

Lemma okt_push_inv : forall Σ E X B,
  okt Σ (E & X ~ B) -> B = bind_typ \/ exists T, B = bind_var T.
Proof.
  introv O; inverts O.
  - false* empty_push_inv.
  - lets (?&?&?): (eq_push_inv H). subst*.
  - lets (?&?&?): (eq_push_inv H). subst*.
Qed.

Lemma okt_strengthen : forall Σ E x U F,
    okt Σ (E & (x ~: U) & F) -> okt Σ (E & F).
  introv O. induction F using env_ind.
  - rewrite concat_empty_r in *. lets*: (okt_push_var_inv O).
  - rewrite concat_assoc in *.
    lets Hinv: okt_push_inv O; inversions Hinv.
    + lets (?&?): (okt_push_typ_inv O).
      applys~ okt_sub.
    + match goal with
      | H: exists T, v = bind_var T |- _ =>
        rename H into Hexists_bindvar end.
      inversions Hexists_bindvar.
      lets (?&?&?): (okt_push_var_inv O).
      applys~ okt_typ. applys* wft_strengthen.
Qed.

Lemma okt_is_wft : forall Σ E x T,
    okt Σ (E & x ~: T) -> wft Σ E T.
  introv Hokt.
  inversion Hokt.
  - false* empty_push_inv.
  - lets (?&?&?): eq_push_inv H. false*.
  - lets (?&?&?): eq_push_inv H. subst.
    match goal with Heq: bind_var ?T1 = bind_var ?T2 |- _ => inversions* Heq end.
Qed.

Lemma okt_is_type : forall Σ E x T,
    okt Σ (E & x ~: T) -> type T.
  introv Hokt. apply okt_is_wft in Hokt. apply* type_from_wft.
Qed.

Ltac unsimpl_map_bind_typ Z P :=
  match goal with
  | |- context [ bind_typ ] =>
    unsimpl (subst_tb Z P bind_typ)
  end.

Lemma wft_type : forall Σ E T,
    wft Σ E T -> type T.
Proof.
  induction 1; eauto.
Qed.

Lemma wft_subst_tb : forall Σ F E Z P T,
  wft Σ (E & (withtyp Z) & F) T ->
  wft Σ E P ->
  ok (E & map (subst_tb Z P) F) ->
  wft Σ (E & map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  introv WT WP. gen_eq G: (E & (withtyp Z) & F). gen F.
  induction WT as [ | | | | ? ? ? ? ? IH | ]; intros F EQ Ok; subst; simpl subst_tt; auto.
  - case_var*.
    + expand_env_empty (E & map (subst_tb Z P) F).
      apply* wft_weaken; fold_env_empty.
    + destruct (binds_concat_inv H) as [?|[? ?]].
      * apply wft_var.
        apply~ binds_concat_right.
        unsimpl_map_bind_typ Z P.
        apply~ binds_map.
      * destruct (binds_push_inv H1) as [[? ?]|[? ?]].
        -- subst. false~.
        -- applys wft_var. apply* binds_concat_left.
  - apply_fresh* wft_all as Y.
    unsimpl ((subst_tb Z P) bind_typ).
    lets: wft_type.
    rewrite* subst_tt_open_tt_var.
    apply_ih_map_bind* IH.
  - econstructor; eauto.
    + introv Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [T' Tand].
      destruct Tand as [Teq Tin].
      rewrite <- Teq.
      apply* H0.
    + apply List.map_length.
Qed.
Hint Resolve wft_subst_tb.

Lemma wft_open : forall Σ E U T1,
  ok E ->
  wft Σ E (typ_all T1) ->
  wft Σ E U ->
  wft Σ E (open_tt T1 U).
Proof.
  introv Ok WA WU. inversions WA. pick_fresh X.
  rewrite* (@subst_tt_intro X).
  lets K: (@wft_subst_tb Σ empty).
  specializes_vars K. clean_empty K. apply* K.
Qed.

(** ** GADT environment properties *)

Hint Resolve okt_is_ok.

Lemma gadt_constructor_ok : forall Σ Name Tarity Ctors Ctor Carity CargType CretTypes,
    binds Name (GADT Tarity Ctors) Σ ->
    List.nth_error Ctors Ctor = Some (GADTconstr Carity CargType CretTypes) ->
    okGadt Σ ->
    okConstructorDef Σ Tarity (GADTconstr Carity CargType CretTypes).
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

Lemma wft_weaken_many : forall Σ As E F T,
    ok (E & F) ->
    wft Σ (E & F) T ->
    (* ok ((add_types E As) & F) -> *)
    (forall A, List.In A As -> A \notin dom E) ->
    (forall A, List.In A As -> A \notin dom F) ->
    DistinctList As ->
    wft Σ ((add_types E As) & F) T.
  induction As; introv Hok HwT HE HF HAs.
  - cbn. eauto.
  - cbn.
    rewrite <- concat_assoc.
    apply* IHAs; try eauto with listin.
    + rewrite concat_assoc.
      eapply adding_free_is_ok; eauto with listin.
    + rewrite concat_assoc.
      apply* wft_weaken.
      eapply adding_free_is_ok; eauto with listin.
    + introv Hin.
      simpl_dom.
      rewrite notin_union.
      split.
      * apply* notin_singleton.
        inversions HAs.
        intro; subst. contradiction.
      * eauto with listin.
    + inversion* HAs.
Qed.

Lemma wft_subst_tb_many : forall Σ (As : list var) (Us : list typ) (E : env bind) (T : typ),
    length As = length Us ->
      wft Σ (add_types E As) T ->
      (forall U, List.In U Us -> wft Σ E U) ->
      (forall A, List.In A As -> A \notin dom E) ->
      DistinctList As ->
      ok E ->
      wft Σ E (subst_tt_many As Us T).
  induction As as [|Ah Ats];
    introv Hlen HwftT WwftUs HE HD Hok;
    destruct Us as [|Uh Uts]; inversion Hlen.
  - cbn.
    cbn in HwftT. eauto.
  - cbn. inversions HD.
    apply IHAts; eauto with listin.
    + cbn in HwftT.
      lets* HS: wft_subst_tb Σ (@EnvOps.empty bind).
      specializes_vars HS.
      clean_empty HS.
      apply* HS.
      * lets* W: wft_weaken_many Σ Ats E (@EnvOps.empty bind) Uh.
        clean_empty W.
        apply W; eauto with listin.
      * lets* OK: adding_free_is_ok_many Ats E (@EnvOps.empty bind).
        clean_empty OK.
        apply OK; eauto with listin.
Qed.

Lemma wft_open_many : forall E Σ Alphas Ts U,
    ok E ->
    length Alphas = length Ts ->
    DistinctList Alphas ->
    (forall A : var, List.In A Alphas -> A \notin dom E) ->
    (forall A : var, List.In A Alphas -> A \notin fv_typ U) ->
    (forall (A : var) (T : typ), List.In A Alphas -> List.In T Ts -> A \notin fv_typ T) ->
    (forall T : typ, List.In T Ts -> wft Σ E T) ->
    wft Σ (add_types E Alphas) (open_tt_many_var Alphas U) ->
    wft Σ E (open_tt_many Ts U).
  introv Hok Hlen Hdistinct FE FU FT WT WU.
  rewrite* (@subst_tt_intro_many Alphas).
  - lets Htb: (@wft_subst_tb_many Σ Alphas Ts).
    specializes_vars Htb.
    clean_empty Htb.
    apply* Htb.
Qed.

Lemma typing_regular : forall Σ E e T,
   {Σ, E} ⊢ e ∈ T -> okt Σ E /\ term e /\ wft Σ E T.
Proof.
  induction 1 as [ |
                   |
                   | ? ? ? ? ? ? ? IH
                   |
                   | ? ? ? ? ? ? ? IH
                   | | | |
                   | ? ? ? ? ? IHval ? IH
                   | ? ? ? ? ? ? ? ? ? ? IH
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
      apply (@wft_open_many E Σ Alphas Ts); eauto;
        intros A; lets* FA: A3 A.
      introv Ain Tin.
      apply* fv_typs_notin.
    + rewrite List.map_length. trivial.
  - pick_fresh y.
    copyTo IH IH1.
    specializes IH y. destructs~ IH.
    forwards* Hctx: okt_push_inv.
    destruct Hctx as [? | Hctx]; try congruence.
    destruct Hctx as [U HU]. inversions HU.
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor. apply* okt_is_type.
      intros. apply* IH1.
    + econstructor.
      apply* okt_is_wft.
      apply_folding E wft_strengthen.
  - splits*.
    destruct IHtyping2 as [? [? Hwft]]. inversion* Hwft.
  - copyTo IH IH1.
    pick_fresh y. specializes IH y.
    add_notin y L. lets HF: IH Fr0. destructs~ HF.
    splits*.
    + forwards*: okt_push_typ_inv.
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
    forwards* Hp: okt_push_inv.
    destruct Hp as [? | Hex]; try congruence.
    destruct Hex as [U HU]. inversions HU.
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor. apply* okt_is_type.
      intros. apply* IH.
      intros. apply* IHval.
    + apply_folding E wft_strengthen.
  - destructs IHtyping.
    pick_fresh y.
    copyTo IH IH1.
    specializes IH y. destructs~ IH.
    forwards* Hctx: okt_push_inv.
    destruct Hctx as [? | Hctx]; try congruence.
    destruct Hctx as [U HU]. inversions HU.
    splits*.
    + econstructor. auto.
      introv HxiL. lets HF: IH1 x HxiL. destruct* HF.
    + apply_folding E wft_strengthen.
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


Lemma typing_implies_term : forall Σ E e T,
    {Σ, E} ⊢ e ∈ T ->
    term e.
  intros.
  lets TR: typing_regular Σ E e T.
  destruct* TR.
Qed.
