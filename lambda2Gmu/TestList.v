Require Import Definitions.
Require Import Psatz.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.

(* TODO merge prelude with Tests.v *)

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).
Ltac fs := exact \{}. (* There must be a better way *)

Axiom List : var.
Definition ListDef := GADT 1 [
                            GADTconstr 1 typ_unit [@0];
                            GADTconstr 1 (@0 ** typ_gadt [@0] List) [@0]
                          ].

Ltac ininv :=
  match goal with
  | H: List.In _ _ |- _ =>
    inversions H
  end.

Definition listSigma := (empty & List ~ ListDef).

Ltac destruct_const_len_list :=
  repeat (match goal with
          | H: length ?L = ?n |- _ =>
            destruct L; inversions H
          end).

Lemma oklist : okGadt listSigma.
  constructor*.
  - constructor.
  - intros; repeat ininv.
    + econstructor.
      * intros. destruct_const_len_list.
        econstructor.
      * intros. destruct_const_len_list.
        repeat ininv.
        econstructor.
        cbn. eauto.
    + econstructor.
      * intros. destruct_const_len_list. econstructor; cbn; econstructor; eauto.
        introv Hin.
        repeat ininv.
        econstructor. eauto.
      * intros.
        destruct_const_len_list.
        repeat ininv.
        econstructor. cbn. eauto.
        Unshelve. fs. fs.
Qed.

Definition nil T := trm_constructor [T] (List, 0) trm_unit.
Definition cons T h t := trm_constructor [T] (List, 1) (trm_tuple h t).

