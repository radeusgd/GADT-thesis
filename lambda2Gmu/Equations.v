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

End SimpleEquationProperties.

Lemma spawn_unit_subst : forall Σ As,
    exists Θ, length Θ = length As /\ subst_matches_typctx Σ (tc_vars As) Θ.
  induction As as [| Ah Ats].
  - cbn.
    exists (@nil (var * typ)).
    split~.
    constructor.
  - destruct IHAts as [LT [Len Match]].
    exists ((Ah, typ_unit) :: LT).
    split.
    + cbn. auto.
    + constructor.
      * constructor.
      * fold (List.map tc_var Ats).
        fold (tc_vars Ats).
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

Lemma only_vars_is_never_contradictory : forall Σ Δ,
    (forall tc, List.In tc Δ -> exists A, tc = tc_var A) ->
    ~ (contradictory_bounds Σ Δ).
  intros.
  intro HF.
  unfold contradictory_bounds in HF.
  lets F: HF typ_unit (typ_unit ** typ_unit).
  unfold entails_semantic in F.
  lets* [As AsEQ]: only_vars_is_tc_vars. subst.
  lets [Θ [TLen TMatch]]: spawn_unit_subst Σ As.
  assert (Contr: typ_unit = typ_unit ** typ_unit).
  - unfold alpha_equivalent in F.
    lets F2: F TMatch.
    rewrite subst_ttΘ_fresh in F2.
    + rewrite~ subst_ttΘ_fresh in F2.
      cbn.
      rewrite union_empty_r.
      rewrite~ inter_empty_r.
    + cbn.
      rewrite~ inter_empty_r.
  - false.
Qed.
