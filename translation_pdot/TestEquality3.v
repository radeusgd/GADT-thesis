Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
Require Import GMu.TestEquality.
Require Import Translation.
Require Import Top.TestEqualityEnv.

Lemma construct_tuple_lemma : forall G A B C D,
    G ⊢ A =:= C ->
    G ⊢ B =:= D ->
    G ⊢ (pvar lib) ↓ Tuple ∧ {T1 == A} ∧ {T2 == B} =:= (pvar lib) ↓ Tuple ∧ {T1 == C} ∧ {T2 == D}.
  introv [] [].
  repeat apply~ eq_and_merge.
Qed.

