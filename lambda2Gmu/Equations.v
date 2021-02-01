Require Import Prelude.
Require Import Infrastructure.

(* Proofs regarding proposition 2.1 from the paper *)

Section SimpleEquationProperties.

  Variable Σ : GADTEnv.

  Lemma teq_reflexivity : forall Δ T,
      entails_semantic Σ Δ (T ≡ T).
    cbn.
    intros.
    unfold alpha_equivalent.
    auto.
  Qed.

  Lemma teq_symmetry : forall Δ T U,
      entails_semantic Σ Δ (T ≡ U) ->
      entails_semantic Σ Δ (U ≡ T).
    cbn. intros.
    unfold alpha_equivalent in *.
    symmetry.
    auto.
  Qed.

  Lemma teq_transitivity : forall Δ T U V,
      entails_semantic Σ Δ (T ≡ U) ->
      entails_semantic Σ Δ (U ≡ V) ->
      entails_semantic Σ Δ (T ≡ V).
    cbn. intros.
    unfold alpha_equivalent in *.
    transitivity (subst_tt' U Θ); auto.
  Qed.

  Lemma subst_tt_inside : forall Θ A P T,
      A \notin substitution_sources Θ ->
      subst_tt' (subst_tt A P T) Θ
      =
      subst_tt A (subst_tt' P Θ) (subst_tt' T Θ).
  Admitted.

  Lemma teq_axiom : forall Δ T U,
      List.In (tc_eq (T ≡ U)) Δ ->
      entails_semantic Σ Δ (T ≡ U).
    unfold entails_semantic. unfold alpha_equivalent.
    induction Δ; introv Hin Hmatch.
    - contradiction.
    - cbn in Hin.
      destruct Hin as [Hin | Hin].
      + subst.
        inversions Hmatch; easy.
      + inversions Hmatch; auto.
        cbn.
        assert (A \notin substitution_sources Θ0); [admit|idtac].
        repeat rewrite subst_tt_inside; auto.
        f_equal.
        apply IHΔ; auto.
  Admitted.

End SimpleEquationProperties.

Ltac fold_from_list :=
  repeat progress match goal with
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

Lemma spawn_unit_subst : forall Σ As,
    DistinctList As ->
    exists Θ, length Θ = length As /\ subst_matches_typctx Σ (tc_vars As) Θ /\ substitution_sources Θ = from_list As.
  induction As as [| Ah Ats]; introv ADist.
  - cbn.
    exists (@nil (var * typ)).
    splits~.
    constructor.
  - inversions ADist.
    destruct IHAts as [LT [Len [Match Src]]]; auto.
    exists ((Ah, typ_unit) :: LT).
    splits.
    + cbn. auto.
    + constructor;
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
  unfold alpha_equivalent in F.
  cbn in F.
  false.
Qed.

Lemma typing_exfalso : forall Σ Δ E e T1 T2,
    {Σ, Δ, E} ⊢ e ∈ T1 ->
    contradictory_bounds Σ Δ ->
    {Σ, Δ, E} ⊢ e ∈ T2.
  introv Typ Bounds.
  apply typing_eq with T1; auto.
Qed.

(* Lemma generalized_inversion : forall Σ Δ E e T, *)
(*     {Σ, Δ, E} ⊢ e ∈ T -> *)
(*     ~ (contradictory_bounds Σ Δ) -> *)
(*     (exists T', okt Σ Δ E /\ T = typ_unit) \/ True. (* TODO other cases: probably instead I want to add some syntactic separation of equations instead of writing a huge inversion here *) *)
(*   introv Typ Bounds. *)
(* Admitted. *)
