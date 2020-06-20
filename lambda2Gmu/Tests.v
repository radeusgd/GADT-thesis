Require Import Definitions.
Require Import TLC.LibLN.
Require Import Infrastructure.

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).

Definition id := trm_tabs (trm_abs (@0) (#0)).
Definition id_typ := typ_all (typ_arrow (@0) (@0)).


Inductive evals : trm -> trm -> Prop :=
| eval_step : forall a b c, a --> b -> evals b c -> evals a c
| eval_finish : forall a, evals a a.


Ltac simpl_op := cbn; try case_if; auto.
Ltac solve_simple_type := repeat ((* let L := gather_vars in try apply typing_abs with L; *) econstructor; eauto; cbn; try case_if; eauto).
Ltac crush_simple_type := repeat (cbv; (try case_if); econstructor; eauto).
Ltac fs := exact \{}. (* There must be a better way *)

Lemma well_formed_id :
  term id
  /\ type id_typ
  /\ wft empty empty id_typ.
  intuition; solve_simple_type.
  Unshelve. fs. fs. fs. fs.
Qed.

Lemma well_typed_id : {empty, empty} ⊢ id ∈ id_typ.
  solve_simple_type.
Qed.

(* Ltac tst := *)
(*   match goal with *)
(*   | H: ?x \notin ?L |- _ => instantiate (1 := \{}) *)
(*   end. *)
(* Ltac tst := *)
(*   match goal with *)
(*   | _:_ |- {?Σ, ?E} ⊢ (trm_abs ?T1 ?e1) open_te_var ?x ∈ (?T open_tt_var ?x) => *)
(*     instantiate (1 := T1 ==> _) *)
(*   end. *)

(* TODO we need an ADT for some Nat numbers type *)
Definition id_id_app := (trm_app (trm_tapp id id_typ) id).
Lemma id_of_id_types : {empty, empty} ⊢ id_id_app ∈ id_typ.
  solve_simple_type.
  - intros.
    (* instantiate (1 := _ ==> _). *)
    instantiate (1 := (@0) ==> @0).
    simpl_op.
    crush_simple_type.
  - intros.
    instantiate (1 := (@0) ==> @0).
    crush_simple_type.
  - simpl_op.
Qed.

Ltac crush_eval := repeat (try (apply eval_finish; eauto); econstructor; simpl_op).

Lemma id_of_id_evals : evals id_id_app id.
  crush_eval.
  Unshelve. fs. fs. fs. fs. fs. fs. fs.
Qed.

