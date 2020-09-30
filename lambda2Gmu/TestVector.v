Require Import Definitions.
Require Import Psatz.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.

(* TODO merge prelude with Tests.v *)

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).
Ltac fs := exact \{}. (* There must be a better way *)

(* type level natural numbers *)
Axiom Zero : var.
Axiom Succ : var.
Axiom Vector : var.

Axiom all_distinct :
  (Zero <> Succ) /\ (Succ <> Vector) /\ (Zero <> Vector).
Definition VectorDef := (* Vector a len *)
  GADT 2 [
         (* empty : () -> Vector a Zero *)
         GADTconstr 1 typ_unit [@0; typ_gadt [] Zero];
         (* cons : (a * Vector a n) -> Vector a (Succ n) *)
         GADTconstr 2 (@0 ** typ_gadt [@0; @1] Vector) [@0; typ_gadt [@1] Succ]
       ].

Definition sigma :=
  empty
  & Zero ~ GADT 0 [] (* zero and succ are phantom types, so they do not even need any constructors (but we can add them if needed) *)
  & Succ ~ GADT 1 []
  & Vector ~ VectorDef.

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

Ltac solve_dom :=
  simpl_dom; notin_solve; try (apply notin_singleton; lets*: all_distinct).

Ltac distinct2 :=
  match goal with
  | H1: DistinctList ?L |- _ =>
    inversions H1;
    match goal with
    | H2: List.In ?v ?L1 -> False |- _ =>
      cbn in H2; eauto
    end
  end.

Lemma oksigma : okGadt sigma.
  constructor*.
  - repeat constructor*; try (introv Hfalse; inversions Hfalse).
    solve_dom.
  - solve_dom.
  - intros; repeat ininv.
    + econstructor.
      * intros. destruct_const_len_list.
        econstructor.
      * intros. destruct_const_len_list.
        repeat ininv.
        -- econstructor.
           cbn. eauto.
        -- econstructor.
           ++ cbn; contradiction.
           ++ cbv; repeat apply* binds_concat_left; solve_dom.
           ++ cbn; eauto.
    + econstructor.
      * intros. destruct_const_len_list. econstructor; cbn; econstructor; eauto.
        -- apply* binds_concat_left.
           solve_dom; distinct2.
        -- intros.
           repeat ininv.
           ++ econstructor. apply* binds_concat_left.
              solve_dom; distinct2.
           ++ econstructor.
              apply* binds_concat_right.
              apply* binds_single_eq.
      * intros. destruct_const_len_list.
        repeat ininv.
        -- cbn. econstructor.
           apply* binds_concat_left.
           solve_dom; distinct2.
        -- cbn.
           econstructor.
           ++ intros; repeat ininv.
              econstructor. apply* binds_concat_right. apply* binds_single_eq.
           ++ apply* binds_concat_left.
              solve_dom.
           ++ cbn. eauto.
        Unshelve. fs. fs.
Qed.

Definition nil A := trm_constructor [A; typ_gadt [] Zero] (Vector, 0) trm_unit.
Definition cons A Len h t := trm_constructor [A; Len] (Vector, 1) (trm_tuple h t).

Lemma nil_type : {sigma, empty} ⊢ (trm_tabs (nil (@0))) ∈ typ_all (typ_gadt [@0; typ_gadt [] Zero] Vector).
Admitted.

(* TODO Lemma cons_type : {sigma, empty} ⊢ (trm_tabs (trm_tabs cons (@0))) ∈ typ_all (typ_gadt [@0; typ_gadt [] Zero] Vector). *)
  
(* Admitted. *)
