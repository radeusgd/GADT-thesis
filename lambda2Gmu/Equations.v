Require Import TLC.LibLN.
Require Import Definitions.
Require Import TLC.LibTactics.
Require Import List.
Import List.ListNotations.

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
