Require Import TestCommon.
Require Import Regularity.

Definition id := trm_tabs (trm_abs (@0) (#0)).
Definition id_typ := typ_all (@0 ==> @0).

Ltac simpl_op := cbn; try case_if; auto.
(* Ltac solve_simple_type := repeat ((* let L := gather_vars in try apply typing_abs with L; *) intros; econstructor; eauto; cbn; try case_if; eauto). *)
Ltac crush_simple_type := repeat (cbv; (try case_if); econstructor; eauto).

Lemma well_typed_id : {empty, emptyΔ, empty} ⊢(Treg) id ∈ id_typ.
  cbv; autotyper1.
Qed.

Lemma well_formed_id :
  term id
  /\ type id_typ
  /\ wft empty emptyΔ id_typ.
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
Lemma id_app_types : {empty, emptyΔ, empty} ⊢(Treg) id_app ∈ typ_unit.
  cbv.
  econstructor.
  - admit.
  - econstructor.
    + econstructor.
      * intros.
  cbv; autotyper1.
  2: {
    instantiate (1 := (@0 ==> @0)).
    cbn. autotyper1. 
  }
  - autotyper1.
  - autotyper1.
Qed.

Ltac crush_eval := repeat (try (apply eval_finish; eauto); econstructor; simpl_op).

Lemma id_app_evals : evals id_app trm_unit.
  crush_eval.
  Unshelve. fs. fs. fs. fs.
Qed.

Definition let_id_app := trm_let (id) (trm_app (trm_tapp (#0) typ_unit) trm_unit).
Lemma let_id_app_types : {empty, emptyΔ, empty} ⊢ let_id_app ∈ typ_unit.
  cbv.
  autotyper1.
  4: {
    instantiate (1 := (@0 ==> @0)).
    cbn. auto.
  }
  autotyper1.
  autotyper1.
  autotyper1.
Qed.

Lemma let_id_app_evals : evals let_id_app trm_unit.
  crush_eval.
  Unshelve.
  fs. fs. fs. fs. fs. fs. fs. fs. fs. fs. fs.
Qed.

Definition loop := trm_fix (typ_unit ==> typ_unit) (trm_abs typ_unit (trm_app (#1) (#0))).

Lemma loop_type : {empty, emptyΔ, empty} ⊢ loop ∈ (typ_unit ==> typ_unit).
  cbv.
  autotyper1.
Qed.

Definition divergent := trm_app loop trm_unit.

Lemma divergent_type : {empty, emptyΔ, empty} ⊢ divergent ∈ typ_unit.
  cbv. autotyper1.
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

