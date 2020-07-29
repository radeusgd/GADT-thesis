Require Import Definitions.
Require Import TLC.LibLN.
Require Import Infrastructure.

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).

Definition id := trm_tabs (trm_abs (@0) (#0)).
Definition id_typ := typ_all (@0 ==> @0).
Inductive evals : trm -> trm -> Prop :=
| eval_step : forall a b c, a --> b -> evals b c -> evals a c
| eval_finish : forall a, evals a a.


Ltac simpl_op := cbn; try case_if; auto.
(* Ltac solve_simple_type := repeat ((* let L := gather_vars in try apply typing_abs with L; *) intros; econstructor; eauto; cbn; try case_if; eauto). *)
Ltac crush_simple_type := repeat (cbv; (try case_if); econstructor; eauto).
Ltac fs := exact \{}. (* There must be a better way *)

Lemma well_typed_id : {empty, empty} ⊢ id ∈ id_typ.
  econstructor.
  - intros.
    constructor*. cbv. case_if. econstructor. econstructor.
    intros. cbv. case_if. econstructor.
  - intros.
    econstructor. cbn. case_if. intros.
    econstructor. eauto. constructor*.
    repeat constructor*.
  Unshelve.
  fs. fs.
Qed.

Lemma well_formed_id :
  term id
  /\ type id_typ
  /\ wft empty empty id_typ.
  destruct* (typing_regular well_typed_id).
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

Definition id_app := (trm_app (trm_tapp id typ_unit) trm_unit).
Lemma id_app_types : {empty, empty} ⊢ id_app ∈ typ_unit.
  econstructor; repeat econstructor; cbn; try case_if.
  - econstructor.
  - intros. econstructor.
  - intros.
    instantiate (1 := (@0 ==> @0)).
    simpl_op.
    crush_simple_type.
  - crush_simple_type.
    Unshelve.
    fs.
Qed.

Ltac crush_eval := repeat (try (apply eval_finish; eauto); econstructor; simpl_op).

Lemma id_app_evals : evals id_app trm_unit.
  crush_eval.
  Unshelve. fs. fs. fs. fs.
Qed.

Definition let_id_app := trm_let (id) (trm_app (trm_tapp (#0) typ_unit) trm_unit).
Lemma let_id_app_types : {empty, empty} ⊢ let_id_app ∈ typ_unit.
  unfold let_id_app.
  econstructor.
  - eapply well_typed_id.
  - crush_simple_type.
    Unshelve.
    fs. fs.
Qed.

Lemma let_id_app_evals : evals let_id_app trm_unit.
  crush_eval.
  Unshelve.
  fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs.
Qed.

Definition loop := trm_fix (typ_unit ==> typ_unit) (trm_abs typ_unit (trm_app (#1) (#0))).

Lemma loop_type : {empty, empty} ⊢ loop ∈ (typ_unit ==> typ_unit).
  cbv.
  econstructor; intros; econstructor; cbn; repeat case_if; econstructor.
  - econstructor.
  - intros. econstructor; cbn; try case_if; econstructor.
  - cbn; case_if; repeat constructor*.
  - repeat constructor*.
    Unshelve. fs. fs.
Qed.

Definition divergent := trm_app loop trm_unit.

Lemma divergent_type : {empty, empty} ⊢ divergent ∈ typ_unit.
  econstructor.
  2: {
    apply loop_type.
  }
  repeat econstructor.
Qed.

Lemma divergent_diverges : evals divergent divergent.
  cbv.
  econstructor.
  - crush_eval.
  - unfold open_ee. cbn; repeat case_if.
    econstructor.
    + crush_eval.
    + repeat case_if.
      apply eval_finish.

      Unshelve.
      fs. fs. fs. fs. fs. fs. fs.
Qed.
