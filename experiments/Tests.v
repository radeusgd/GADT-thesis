Require Import Lam2Gmu.
Require Import TLC.LibLN.

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).

Definition id := trm_tabs (trm_abs (@0) (#0)).
Definition id_typ := typ_all (typ_arrow (@0) (@0)).

Hint Constructors type term wft.

Lemma well_formed_id :
  term id
  /\ type id_typ
  /\ wft empty empty id_typ.
  intuition.
  (* TODO create tactics to automate such simple proofs *)
  - econstructor. intros.
    econstructor; cbn; case_if. econstructor.
    intros.
    econstructor.
  - econstructor.
    intros.
    repeat (econstructor; case_if).
  - econstructor.
    intros.
    econstructor; case_if; econstructor.
    + eauto.
    + eauto.
      (* TODO FIXME:
All the remaining goals are on the shelf.
subgoal 1 (ID 794) is:
 fset var
Error: Attempt to save a proof with shelved goals (in proof well_formed_id)
      *)
Admitted.

(* Lemma well_typed_id : empty empty ⊢ id :~ id_typ. *)
