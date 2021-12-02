Require Import Helpers.
Require Import TestHelpers.

Lemma simple_eq_and_rule_would_be_unsound :
    (forall G X1 X2 A T U,
        G ⊢ X1 ∧ {A == T} =:= X2 ∧ {A == U} ->
        G ⊢ T =:= U
    ) ->
    forall (A : typ_label),
    forall G X Y,
      G ⊢ X =:= Y.
  introv R.
  intros.
  apply R with ⊥ ⊥ A.
  apply eq_transitive with ({A == X} ∧ ⊥).
  1: {
    apply eq_and_comm.
  }

  apply eq_transitive with ({A == Y} ∧ ⊥).
  2: {
    apply eq_and_comm.
  }

  apply eq_and_bot_exfalso.
Qed.

(* This is actually not enough yet because we still have the lib.Tuple etc. references, but first approximation... *)
Inductive has_only_objects_or_top : typ -> Prop :=
| only_top : has_only_objects_or_top ⊤
| only_val : forall x T, has_only_objects_or_top { x ⦂ T}
| only_typ : forall A T U, has_only_objects_or_top { A >: T <: U }
| only_and : forall T1 T2,
    has_only_objects_or_top T1 ->
    has_only_objects_or_top T2 ->
    has_only_objects_or_top (T1 ∧ T2)
.

Lemma obj_only_eq_and_rule_would_be_unsound :
  (forall G X1 X2 A T U,
      G ⊢ X1 ∧ {A == T} =:= X2 ∧ {A == U} ->
      has_only_objects_or_top X1 ->
      has_only_objects_or_top X2 ->
      G ⊢ T =:= U
    ) ->
    forall (A : typ_label),
    forall G X Y,
      G ⊢ X =:= Y.
  introv R.
  intros.
  assert (HF: G ⊢ {A == ⊤} ∧ {A == ⊥} =:= {A == ⊥} ∧ {A == ⊤}).
  - assert (G ⊢ {A == ⊤} ∧ {A == ⊥} =:= {A == ⊤} ∧ {A == ⊥})
      by apply eq_reflexive.
    eapply eq_transitive.
    + apply eq_and_comm.
    + auto.
  - apply eq_exfalso.
    apply eq_symmetry.
    lets~ F: R HF.
    apply F; constructor.
Qed.

(*

Further ideas:

We can try further restricting the 'domain' of X1, X2, for example to ensure it only has unique type lables.

But even our example 'indirectly' violates this:

lib.Tuple /\ {T1 == X} /\ {T2 == Y} =:= lib.Tuple /\ {T1 == Z} /\ {T2 == W}

where lib.Tuple == { T1 >: ⊥ <: ⊤ } ∧ { T2 >: ⊥ <: ⊤ } ∧ { fst_v ⦂ this ↓ T1 } ∧ { snd_v ⦂ this ↓ T2 }

LibraryExperiments shows that we may try defining the Tuples (and analogusly GADTs) skipping the types that have these 'unlimited' bounds.

So the uniqueness assumption may be a viable path forwards, but it will require a very specific and careful rule to work.

Especially as the Tuple example foreshadows, we need uniqueness to be defined in the context of the whole environment, not just the type.
*)

Lemma weak_uniqueness_eq_and_rule_would_be_unsound :
  (forall G X1 X2 A T U,
      G ⊢ X1 ∧ {A == T} =:= X2 ∧ {A == U} ->
      (* I skip the type-based uniqueness definition in assumptions but I promise I will ensure the proof only forms conditions that are unique *)
      G ⊢ T =:= U
    ) ->
  forall (B A : typ_label) (lib : var),
    (* I will extend the environment, but the term to get such an env is a simple legal let-term, we can always have such a term in the environment, so a valid extension would need to be resilient to it anyway. *)
    forall G X Y,
      G & lib ~ typ_rcd {B == {A == ⊤} } ⊢ X =:= Y.
  introv R.
  intros.
  remember (G & lib ~ typ_rcd {B == {A == ⊤} }) as G1.
  assert (HF: G1 ⊢ (pvar lib ↓ B) ∧ {A == ⊥} =:= {A == ⊥} ∧ (pvar lib ↓ B)).
  - assert (G1 ⊢ (pvar lib ↓ B) ∧ {A == ⊥} =:= (pvar lib ↓ B) ∧ {A == ⊥})
      by apply eq_reflexive.
    eapply eq_transitive.
    + apply eq_and_comm.
    + auto.
  - apply eq_exfalso.
    apply eq_symmetry.
    assert (HF2: G1 ⊢ (pvar lib ↓ B) ∧ {A == ⊥} =:= {A == ⊥} ∧ {A == ⊤}).
    + apply eq_transitive with ({A == ⊤} ∧ {A == ⊥}).
      * apply~ eq_and_merge.
        apply eq_symmetry.
        apply eq_sel.
        apply ty_var.
        rewrite HeqG1.
        solve_bind.
      * apply eq_and_comm.
    + lets~ F: R HF2.
Qed.

(*
So the above example shows that we need a strong uniqueness rule:
The conjunction not only must have unique type labels, but if it intersects other type labels like lib.B above, they must resolve in the environment to also not have any additional occurrences of the same label.

An ultimate solution would be to require uniqueness and has_only_objects_or_top as defined above. This is a strong requirement, but it may be enough, since we should always be able to 'resolve' the labels to concrete types from the environment. Thus such a rule will still be usable in our practice, and it will be easier to check the uniqueness requirement - as it will only have to check the type, because it cannot refer to any labels at the base level due to thehas_only_objects_or_top requirement.
*)
