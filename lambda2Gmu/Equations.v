Require Import Prelude.
Require Import Infrastructure.

Ltac fold_from_list :=
  repeat progress
         match goal with
         | [ H: context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} ?L]  |- _ ] =>
           fold (from_list L) in H
         | |- context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} ?L] =>
           fold (from_list L)
         end.

Lemma notin_from_list : forall As (A : var),
    ~ (List.In A As) ->
    A \notin from_list As.
  intros.
  intro HF.
  lets [A' [Hin Heq]]: in_from_list HF.
  subst.
  auto.
Qed.

Lemma inv_distinct : forall l a,
    DistinctList (l ++ [a]) ->
    ~ List.In a l /\ DistinctList l.
  induction l.
  - cbn. intros. split~. constructor.
  - introv D.
    inversions D.
    apply IHl in H2. destruct H2.
    split~.
    + introv In.
      cbn in In.
      destruct In; subst.
      * apply H1. apply List.in_or_app; right; cbn; auto.
      * auto.
    + constructor; auto.
      introv In.
      apply H1.
      apply List.in_or_app. auto.
Qed.

Lemma tc_vars_app : forall a b,
    tc_vars (a ++ b) = tc_vars a ++ tc_vars b.
  introv. unfold tc_vars.
  rewrite List.map_app. auto.
Qed.

Lemma list_in_inv_r : forall T (L : list T) A B,
    List.In A (L ++ [B]) ->
    List.In A L \/ A = B.
  intros.
  apply List.in_app_or in H.
  destruct~ H.
  right. inversion~ H.
  inversion H0.
Qed.

Ltac lister :=
  match goal with
  | [ H: context [tc_vars (?l ++ [?a]) ] |- _ ] =>
    rewrite tc_vars_app in H; cbn in H
  | [ |- context [tc_vars (?l ++ [?a]) ] ] =>
    rewrite tc_vars_app; cbn
  | [ H: DistinctList (?l ++ [?a]) |- _ ] =>
    apply inv_distinct in H; destruct H
  | [ H: context [length (?a ++ ?b) ] |- _ ] =>
    rewrite List.app_length in H
  | [ |- context [length (?a ++ ?b) ] ] =>
    rewrite List.app_length
  | [H: List.In ?X (?L ++ [?Y]) |- _] =>
    apply list_in_inv_r in H
  end.
Ltac autodestruct :=
  match goal with
  | [ H: ?A \/ ?B |- _ ] => destruct H
  | [ H: ?A /\ ?B |- _ ] => destruct H
  | [ H: (?a,?b) = (?c,?d) |- _ ] => inversions* H
  end.

Tactic Notation "lister *" :=
  repeat progress (lister; repeat progress autodestruct; auto).

(* Proofs regarding proposition 2.1 from the paper *)
Section SimpleEquationProperties.

  Variable Σ : GADTEnv.

  Lemma teq_reflexivity : forall Δ T,
      entails_semantic Σ Δ (T ≡ T).
    cbn.
    intros.
    auto.
  Qed.

  Lemma teq_symmetry : forall Δ T U,
      entails_semantic Σ Δ (T ≡ U) ->
      entails_semantic Σ Δ (U ≡ T).
    cbn. intros.
    symmetry.
    auto.
  Qed.

  Lemma teq_transitivity : forall Δ T U V,
      entails_semantic Σ Δ (T ≡ U) ->
      entails_semantic Σ Δ (U ≡ V) ->
      entails_semantic Σ Δ (T ≡ V).
    cbn. intros.
    transitivity (subst_tt' U Θ); auto.
  Qed.

  Lemma subst_has_no_fv : forall Σ Δ Θ,
      subst_matches_typctx Σ Δ Θ ->
      (forall X U, List.In (X, U) Θ -> fv_typ U = \{}).
    induction 1; introv Hin.
    - false.
    - lister*.
      + apply* IHsubst_matches_typctx.
      + lets Hfv: wft_gives_fv H.
        cbn in Hfv.
        apply~ fset_extens.
    - apply* IHsubst_matches_typctx.
  Qed.

  Lemma teq_axiom : forall Δ T U,
      List.In (tc_eq (T ≡ U)) Δ ->
      entails_semantic Σ Δ (T ≡ U).
    unfold entails_semantic.
    induction Δ using List.rev_ind; introv Hin M.
    - contradiction.
    - lister*.
      + subst. invert_subst_match.
        * 
        * admit.
        * 
        * cbn.
          repeat rewrite subst_tt_inside; auto.
          -- f_equal.
             apply IHΔ; auto.
          -- introv Uin.
             lets Fr: subst_has_no_fv Uin.
             ++ eauto.
             ++ rewrite Fr. apply notin_empty.
          -- introv Uin.
             lets Fr: subst_has_no_fv Uin.
             ++ eauto.
             ++ rewrite Fr. apply notin_empty.
        * apply* IHΔ.
      + inversions Hin. invert_subst_match.
        auto.
  Qed.

End SimpleEquationProperties.


Lemma spawn_unit_subst : forall Σ As,
    DistinctList As ->
    exists Θ, length Θ = length As /\ subst_matches_typctx Σ (tc_vars As) Θ /\ substitution_sources Θ = from_list As.
  induction As as [| Ah Ats] using List.rev_ind; introv ADist.
  - cbn.
    exists (@nil (var * typ)).
    splits~.
    constructor.
  - lister*.
    destruct IHAts as [LT [Len [Match Src]]]; auto.
    exists (LT ++ [(Ah, typ_unit)]).
    splits.
    + cbn. lister*.
    + apply tc_add_var.
      constructor.
        fold (List.map tc_var Ats);
        fold (tc_vars Ats);
        auto.
      * rewrite Src.
        apply~ notin_from_list.
      * apply notin_dom_tc_vars.
        apply~ notin_from_list.
    + cbn.
      fold_from_list.
      fold (substitution_sources LT).
      rewrite Src.
      trivial.
Qed.

Lemma only_vars_is_tc_vars : forall Δ,
    (forall tc, List.In tc Δ -> exists A, tc = tc_var A) ->
    exists As, Δ = tc_vars As.
  induction Δ as [| [A | eq] Δt].
  - cbn. intros. exists (@nil var). cbn. trivial.
  - cbn. intro Hin.
    lets* [Ats EQ]: IHΔt.
    exists (A :: Ats). cbn.
    fold (tc_vars Ats).
    f_equal.
    auto.
  - cbn. intro Hin.
    false~ Hin. congruence.
Qed.

Lemma contradictory_env_test_0 : forall Σ Δ,
    entails_semantic Σ Δ (typ_unit ≡ (typ_unit ** typ_unit)) ->
    contradictory_bounds Σ Δ.
  introv Heq.
  unfold contradictory_bounds.
  intros.
  unfold entails_semantic in *.
  introv Hmatch.
  exfalso.
  lets HF: Heq Hmatch.
  rewrite subst_ttΘ_fresh in HF.
  - rewrite subst_ttΘ_fresh in HF.
    + false.
    + cbn. rewrite union_empty_r.
      rewrite~ inter_empty_r.
  - cbn.
    rewrite~ inter_empty_r.
Qed.

Lemma subst_ttΘ_into_abs : forall Θ A B,
    subst_tt' (A ==> B) Θ
    =
    (subst_tt' A Θ) ==> (subst_tt' B Θ).
  induction Θ as [| [X T] Θ]; cbn in *; trivial.
Qed.
Lemma subst_ttΘ_into_tuple : forall Θ A B,
    subst_tt' (A ** B) Θ
    =
    (subst_tt' A Θ) ** (subst_tt' B Θ).
  induction Θ as [| [X T] Θ]; cbn in *; trivial.
Qed.

Lemma contradictory_env_test : forall Σ Δ A B C D,
    entails_semantic Σ Δ ((A ==> B) ≡ (C ** D)) ->
    contradictory_bounds Σ Δ.
  introv Heq.
  unfold contradictory_bounds.
  intros.
  unfold entails_semantic in *.
  introv Hmatch.
  exfalso.
  lets HF: Heq Hmatch.
  rewrite subst_ttΘ_into_abs in HF.
  rewrite subst_ttΘ_into_tuple in HF.
  congruence.
Qed.

(* Lemma only_vars_is_never_contradictory : forall Σ Δ, *)
(*     (forall tc, List.In tc Δ -> exists A, tc = tc_var A) -> *)
(*     ~ (contradictory_bounds Σ Δ). *)
(*   intros. *)
(*   intro HF. *)
(*   unfold contradictory_bounds in HF. *)
(*   lets F: HF typ_unit (typ_unit ** typ_unit). *)
(*   unfold entails_semantic in F. *)
(*   lets* [As AsEQ]: only_vars_is_tc_vars. subst. *)
(*   lets [Θ [TLen TMatch]]: spawn_unit_subst Σ As. *)
(*   assert (Contr: typ_unit = typ_unit ** typ_unit). *)
(*   - unfold alpha_equivalent in F. *)
(*     lets F2: F TMatch. *)
(*     rewrite subst_ttΘ_fresh in F2. *)
(*     + rewrite~ subst_ttΘ_fresh in F2. *)
(*       cbn. *)
(*       rewrite union_empty_r. *)
(*       rewrite~ inter_empty_r. *)
(*     + cbn. *)
(*       rewrite~ inter_empty_r. *)
(*   - false. *)
(* Qed. *)
Lemma adding_var_is_not_contradictory : forall Σ Δ A,
    ~ (contradictory_bounds Σ Δ) ->
    ~ (contradictory_bounds Σ (Δ |,| [tc_var A])).
  introv Hsmal.
  intro HF.
  apply Hsmal.
Admitted.

Lemma adding_vars_is_not_contradictory : forall Σ Δ As,
    ~ (contradictory_bounds Σ Δ) ->
    ~ (contradictory_bounds Σ (Δ |,| tc_vars As)).
  introv Hsmal.
  induction As.
  - cbn. clean_empty_Δ. auto.
  - cbn. fold (tc_vars As).
  intro HF.
  apply Hsmal.
Admitted.

Lemma empty_is_not_contradictory : forall Σ,
    ~ (contradictory_bounds Σ emptyΔ).
  intros.
  intro HF.
  unfold contradictory_bounds in HF.
  asserts M: (subst_matches_typctx Σ emptyΔ (@nil (var*typ)));
    try econstructor.
  lets F: HF typ_unit (typ_unit ** typ_unit) (@nil (var * typ)) M.
  cbn in F.
  false.
Qed.

Lemma typing_exfalso : forall Σ Δ E e T1 T2 TT,
    {Σ, Δ, E} ⊢(TT) e ∈ T1 ->
    contradictory_bounds Σ Δ ->
    wft Σ Δ T2 ->
    {Σ, Δ, E} ⊢(Tgen) e ∈ T2.
  introv Typ Bounds.
  eapply typing_eq; eauto.
Qed.

Lemma inversion_typing_eq : forall Σ Δ E e T TT,
    {Σ, Δ, E} ⊢(TT) e ∈ T ->
    exists T',
      {Σ, Δ, E} ⊢(Treg) e ∈ T' /\ entails_semantic Σ Δ (T ≡ T').
  introv Htyp.
  lets Htyp2: Htyp.
  induction Htyp;
    try match goal with
        | [ H: {Σ, Δ, E} ⊢(Treg) ?e ∈ ?T |- _ ] =>
          exists T; split~; auto using teq_reflexivity
        end.
  lets [T' [IHTyp IHeq]]: IHHtyp Htyp.
  exists T'.
  split~.
  eauto using teq_symmetry, teq_transitivity.
Qed.

Lemma subst_has_no_fv2 : forall Σ Δ Θ Y,
    subst_matches_typctx Σ Δ Θ ->
    (forall A U, List.In (A, U) Θ -> Y \notin fv_typ U).
  introv M Hin.
  lets EQ: subst_has_no_fv M Hin.
  rewrite EQ.
  auto.
Qed.
