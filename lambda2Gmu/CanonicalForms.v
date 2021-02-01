Require Import Definitions.
Require Import Infrastructure.
Require Import Equations.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

(* TODO add assumptions that Δ is not contradictory *)
  (* Ht : {Σ, empty}⊢ trm_constructor Tparams Name e1 ∈ T1 ** T2 *)
Lemma CanonicalConstructorType : forall Σ Δ E Tparams Name Ctor e1 T,
    {Σ, Δ, E} ⊢ trm_constructor Tparams (Name, Ctor) e1 ∈ T ->
    ~ (contradictory_bounds Σ Δ) ->
    (* TODO can we make Typs more specific? *)
    exists Typs, T = typ_gadt Typs Name.
  introv Htyp Hbound.
  inversions Htyp.
  - rewrite rewrite_open_tt_many_gadt.
    eexists.
    f_equal.
  - destruct T.
Admitted.

Lemma CanonicalConstructorTypeGen : forall Σ Δ E Tparams Ctor e1 T,
    {Σ, Δ, E} ⊢ trm_constructor Tparams Ctor e1 ∈ T ->
    ~ (contradictory_bounds Σ Δ) ->
    (* TODO can we make Typs more specific? *)
    exists Typs Name, T = typ_gadt Typs Name.
  intros.
  destruct Ctor.
  apply CanonicalConstructorType in H; auto.
  destruct H as [Typs Heq].
  eexists. eexists. eauto.
Qed.

#[export] Hint Resolve CanonicalConstructorTypeGen.

Ltac contradictory_constructor_type :=
  lazymatch goal with
  | H: {?S, ?D, ?E} ⊢ trm_constructor ?Ts ?C ?e ∈ ?T |- _ =>
    apply CanonicalConstructorTypeGen in H;
    let Hcontradict := fresh "contradict" in
    destruct H as [? [? Hcontradict]];
    inversion Hcontradict
  end.

Lemma CanonicalFormTuple : forall Σ Δ E e T1 T2,
    value e ->
    {Σ, Δ, E} ⊢ e ∈ T1 ** T2 ->
    exists v1 v2, e = trm_tuple v1 v2.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  (* contradictory_constructor_type. *)
Admitted.

Lemma CanonicalFormAbs : forall Σ Δ E e T1 T2,
    value e ->
    {Σ, Δ, E} ⊢ e ∈ T1 ==> T2 ->
    exists v1, e = trm_abs T1 v1.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  (* contradictory_constructor_type. *)
Admitted.

Lemma CanonicalFormTAbs : forall Σ Δ E e T,
    value e ->
    {Σ, Δ, E} ⊢ e ∈ typ_all T ->
    exists v1, e = trm_tabs v1.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  (* contradictory_constructor_type. *)
Admitted.

Lemma CanonicalFormUnit : forall Σ Δ E e,
    value e ->
    {Σ, Δ, E} ⊢ e ∈ typ_unit ->
    e = trm_unit.
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  (* contradictory_constructor_type. *)
Admitted.

Lemma CanonicalFormGadt : forall Σ Δ E e Ts N,
    value e ->
    {Σ, Δ, E} ⊢ e ∈ typ_gadt Ts N ->
    exists Ts' C v, e = trm_constructor Ts' (N, C) v. (* todo may want to relate Ts' to Ts *)
  introv Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  (* rewrite rewrite_open_tt_many_gadt in H8. *)
  (* inversions H8. *)
  (* inversions H12. *)
  (* repeat eexists. *)
Admitted.
