Require Import TLC.LibLN.
Require Import Definitions.
Require Import TLC.LibTactics.
Require Import List.
Import List.ListNotations.

Section TypCtxDefEquivalence.
  (* Here we present the typctx defined precisely as in the paper and show that these two notions are essentially equivalent *)

Inductive typctx_elem : Set :=
| tc_var (A : var)
| tc_eq (eq : type_equation).

(* we keep the elements in reverse order, i.e. the head is the last added element *)
Definition typctx' := list typctx_elem.

Fixpoint translate (Δ' : typctx') : typctx :=
  match Δ' with
  | [] => emptyΔ
  | (tc_var A) :: Δ'' => add_var (translate Δ'') A
  | (tc_eq eq) :: Δ'' => add_eq  (translate Δ'') eq
  end.

Inductive subst_matches_typctx' Σ : typctx' -> substitution -> Prop :=
| tc_empty : subst_matches_typctx' Σ [] []
| tc_add_var : forall Θ Δ A T,
    wft Σ (translate Δ) T ->
    subst_matches_typctx' Σ Δ Θ ->
    subst_matches_typctx' Σ (tc_var A :: Δ) ((A, T) :: Θ)
| tc_add_eq : forall Θ Δ T1 T2,
    subst_matches_typctx' Σ Δ Θ ->
    alpha_equivalent (subst_tt' T1 Θ) (subst_tt' T2 Θ) ->
    subst_matches_typctx' Σ (tc_eq (T1 ≡ T2) :: Δ) Θ.

(* TODO move this to proper place *)
Lemma wft_strengthen_var : forall T Σ Δ A,
    wft Σ Δ T ->
    wft Σ (add_var Δ A) T.
  induction 1; econstructor; eauto.
  - destruct Δ as [vars ?].
    cbn in *. auto.
  - apply H0.


Lemma wft_strengthen_var : forall T Σ Δ A,
    wft Σ Δ T ->
    wft Σ (add_var Δ A) T.

Theorem equivalence : forall Δ' Θ Σ Δ,
    okGadt Σ ->
    translate Δ' = Δ ->
    subst_matches_typctx' Σ Δ' Θ <-> subst_matches_typctx Σ Δ Θ
    .
  induction Δ'; introv HokΣ Htranslate.
  - cbn in Htranslate. subst.
    intuition.
    + inversions H.
      unfold subst_matches_typctx.
      splits*.
      * intros; contradiction.
      * intros; contradiction.
    + destruct H as [? [? ?]].
      cbn in *.
      destruct Θ.
      * econstructor.
      * exfalso.
        cbn in H.
        congruence.
  - destruct a. cbn in Htranslate.
    + destruct Θ as [| (A',T') Θ'].
      * intuition.
        -- inversion H.
        -- inversion H as [? [? ?]].
           destruct Δ as [vars ?].
           cbn in *.
           subst.
           inversion Htranslate.
      * lets* [IH1 IH2]: IHΔ' Θ' Σ (translate Δ').
        intuition.
        -- inversions H.
           lets [IHA [IHB IHC]]: IH1 H6.
           unfold subst_matches_typctx.
           splits*.
           ++ cbn. rewrite <- IHA. auto.
           ++ 
    + 
    Admitted.



End TypCtxDefEquivalence.
