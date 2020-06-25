Require Import Definitions.
Require Import Infrastructure.
Require Import TLC.LibTactics.
Require Import TLC.LibEnv.
Require Import TLC.LibLN.

Lemma CanonicalFormTuple : forall Σ e T1 T2,
    value e ->
    {Σ, empty} ⊢ e ∈ T1 ** T2 ->
    exists v1 v2, e = trm_tuple v1 v2.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; congruence.
Qed.

Lemma CanonicalFormAbs : forall Σ e T1 T2,
    value e ->
    {Σ, empty} ⊢ e ∈ T1 ==> T2 ->
    exists v1, e = trm_abs T1 v1.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; congruence.
Qed.

Lemma CanonicalFormTAbs : forall Σ e T,
    value e ->
    {Σ, empty} ⊢ e ∈ typ_all T ->
    exists v1, e = trm_tabs v1.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; congruence.
Qed.

Lemma CanonicalFormUnit : forall Σ e,
    value e ->
    {Σ, empty} ⊢ e ∈ typ_unit ->
    e = trm_unit.
  introv.
  intros Hv Ht.
  inversion Hv; inversion Ht; subst; eauto; congruence.
Qed.
