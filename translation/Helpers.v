Require Export Predefs.
Require Export TLC.LibTactics.
Require Export TLC.LibLN.
Require Export GMu.Prelude.
Require Export Definitions.


Require Export Lists.List.
Export ListNotations.
Require Export ExampleTactics.

Notation "'{' A '==' T '}'" := (dec_typ A T T).
Coercion typ_rcd : dec >-> Target.typ.
Notation "'{(' a , .. , c ')}'" := (defs_cons (.. (defs_cons defs_nil a) ..) c).
Coercion trm_val  : val >-> trm.
(* TODO not sure if this is not too many coercions... *)
Coercion defp : path >-> def_rhs.
Coercion defv : val >-> def_rhs.

Lemma intersection_order : forall G A1 B1 A2 B2,
    G ⊢ A1 <: A2 ->
              G ⊢ B1 <: B2 ->
                        G ⊢ A1 ∧ B1 <: A2 ∧ B2.
  intros.
  apply subtyp_and2.
  - apply subtyp_trans with A1; auto.
  - apply subtyp_trans with B1; auto.
Qed.
