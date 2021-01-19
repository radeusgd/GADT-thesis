Require Export Prelude.
Require Import Psatz.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.
Require Import Infrastructure.

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).
Ltac fs := exact \{}.

Ltac ininv :=
  match goal with
  | H: List.In _ _ |- _ =>
    inversions H
  end.

Ltac destruct_const_len_list :=
  repeat (match goal with
          | H: length ?L = ?n |- _ =>
            destruct L; inversions H
          end).

Ltac binds_inv :=
  match goal with
  | H: binds ?x ?a empty |- _ =>
    apply binds_empty_inv in H; contradiction
  | H: binds ?x ?a ?E |- _ =>
    binds_cases H;
    try match goal with
        | H: binds ?x ?a empty |- _ =>
          apply binds_empty_inv in H; contradiction
        end;
    subst
  | |- ?x \notin \{ ?y } =>
    apply* notin_inverse
  end.

Ltac solve_dom all_distinct :=
  simpl_dom; notin_solve; try (apply notin_singleton; lets*: all_distinct).

Ltac distinct2 :=
  match goal with
  | H1: DistinctList ?L |- _ =>
    inversions H1;
    match goal with
    | H2: ~ List.In ?v ?L1 |- _ =>
      cbn in H2; eauto
    end
  end.

Ltac solve_bind_core :=
  lazymatch goal with
  | |- binds ?Var ?What (?Left & ?Right) =>
    match goal with
    | |- binds Var What (Left & Var ~ ?Sth) =>
      apply* binds_concat_right; apply* binds_single_eq
    | _ => apply* binds_concat_left
    end
  end.

Ltac solve_bind :=
  (repeat solve_bind_core); try (solve_dom).

Export Definitions.
Export Psatz.
Export TLC.LibLN.
Export TLC.LibEnv.
Export Infrastructure. (* TODO only the gathering parts, should be split out *)

Inductive evals : trm -> trm -> Prop :=
| eval_step : forall a b c, a --> b -> evals b c -> evals a c
| eval_finish : forall a, evals a a.

Lemma is_var_defined_split : forall A B c, (is_var_defined A c \/ is_var_defined B c) -> is_var_defined (A |,| B) c.
  unfold is_var_defined.
  intros.
  apply List.in_or_app. auto.
Qed.

Ltac autotyper1 :=
  repeat progress (
           cbn;
           match goal with
           | [ H: False |- _ ] => false*
           | [ |- ok ?A ] => econstructor
           | [ |- okt ?A ?B ?C ] => econstructor
           | [ |- binds ?A ?B ?C ] => solve_bind
           | [ |- ?A \notin ?B ] => simpl_dom; notin_solve; try (apply notin_singleton)
           | [ |- typing ?A ?B ?C ?D ?E ] => econstructor
           | [ |- forall x, x \notin ?L -> ?P ] =>
             let free := gather_vars in
             let x' := fresh "x" in
             let xiL := fresh "xiL" in
             intros x' xiL; intros;
             try instantiate (1 := free) in xiL
           | [ |- okGadt empty ] => econstructor
           | [ |- wft ?A ?B ?C ] => econstructor
           | [ |- value ?A ] => econstructor
           | [ |- term ?A ] => econstructor
           | [ |- type ?A ] => econstructor
           | [ H: binds ?A ?B ?C |- _ ] => binds_inv
           | [ |- ?A /\ ?B ] => split
           | [ H: {| Tarity := ?A; Tconstructors := ?B |} = ?C |- _ ] =>
             inversions H
           | [ H: ?A \/ ?B |- _ ] => destruct H
           | [ |- is_var_defined (?A |,| ?B) ?c ] => apply is_var_defined_split
           | _ => intros; auto
           end;
           cbn; subst).
