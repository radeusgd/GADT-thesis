Require Import Definitions.
Require Import Infrastructure.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

  (* Ht : {Σ, empty}⊢ trm_constructor Tparams Name e1 ∈ T1 ** T2 *)
Lemma CanonicalConstructorType : forall Σ E Tparams Name Ctor e1 T,
    {Σ, E} ⊢ trm_constructor Tparams (Name, Ctor) e1 ∈ T ->
    (* TODO can we make Typs more specific? *)
    exists Typs, T = typ_gadt Typs Name.
  introv Htyp.
Admitted.

Lemma CanonicalConstructorTypeGen : forall Σ E Tparams Ctor e1 T,
    {Σ, E} ⊢ trm_constructor Tparams Ctor e1 ∈ T ->
    (* TODO can we make Typs more specific? *)
    exists Typs Name, T = typ_gadt Typs Name.
  intros.
  destruct Ctor.
  apply CanonicalConstructorType in H.
  destruct H as [Typs Heq].
  eexists. eexists. eauto.
Qed.

Hint Resolve CanonicalConstructorTypeGen.

Lemma CanonicalFormTuple : forall Σ e T1 T2,
    value e ->
    {Σ, empty} ⊢ e ∈ T1 ** T2 ->
    exists v1 v2, e = trm_tuple v1 v2.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  -
    admit.
  (*  An inversion lemma that detects impossible GADTs would be useful  *)
Admitted.

Lemma CanonicalFormAbs : forall Σ e T1 T2,
    value e ->
    {Σ, empty} ⊢ e ∈ T1 ==> T2 ->
    exists v1, e = trm_abs T1 v1.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  - admit.
Admitted.

Lemma CanonicalFormTAbs : forall Σ e T,
    value e ->
    {Σ, empty} ⊢ e ∈ typ_all T ->
    exists v1, e = trm_tabs v1.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  - admit.
Admitted.

Lemma CanonicalFormUnit : forall Σ e,
    value e ->
    {Σ, empty} ⊢ e ∈ typ_unit ->
    e = trm_unit.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; try congruence.
  - admit.
Admitted.
