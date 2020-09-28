Require Import Definitions.
Require Import Psatz.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.

(* TODO merge with Tests.v *)

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).
Ltac fs := exact \{}. (* There must be a better way *)

Axiom Nat : var.
Definition NatDef := GADT 0 [
                            GADTconstr 0 typ_unit [];
                            GADTconstr 0 (typ_gadt [] Nat) []
                          ].

Ltac ininv :=
  match goal with
  | H: List.In _ _ |- _ =>
    inversions H
  end.

Definition natSigma := (empty & Nat ~ NatDef).

Lemma oknat : okGadt natSigma.
  constructor*.
  - constructor.
  - intros; repeat ininv.
    + econstructor.
      * intros. destruct Alphas; inversions H; econstructor.
      * intros. intuition.
    + econstructor.
      * intros. destruct Alphas; inversions H; econstructor.
        intros.
        inversion H.
        auto. auto.
      * intros. intuition.
        Unshelve. fs. fs.
Qed.

Hint Immediate oknat.

Definition zero := trm_constructor [] (Nat, 0) trm_unit.

Lemma zero_type : {natSigma, empty} ⊢ zero ∈ typ_gadt [] Nat.
  cbv.
  econstructor; eauto.
  - cbn.
    econstructor; econstructor; apply* oknat.
  - cbn.
    instantiate (2:=0).
    assert (Hz: forall x, x * 0 = 0); try (intros; lia).
    rewrite* Hz.
  - cbv. eauto.
Qed.

Require Import Psatz.
Definition one := trm_constructor [] (Nat, 1) zero.
Lemma one_type : {natSigma, empty} ⊢ one ∈ typ_gadt [] Nat.
  cbv.
  econstructor; eauto.
  - cbn. econstructor; eauto.
    + econstructor. econstructor. apply* oknat.
    + cbn. f_equal.
    instantiate (2:=0).
    cbn.
    eauto.
  - cbn; f_equal.
    instantiate (2:=0). eauto.
  - cbn. eauto.
Qed.

Definition succ := trm_abs (typ_gadt [] Nat) (trm_constructor [] (Nat, 1) (#0)).

Lemma succ_type : {natSigma, empty} ⊢ succ ∈ (typ_gadt [] Nat) ==> (typ_gadt [] Nat).
  cbv.
  econstructor.
  intros.
  econstructor; eauto.
  - cbn.
    econstructor; eauto.
    econstructor; eauto.
    + econstructor; eauto using oknat.
    + econstructor; eauto.
      intros. contradiction.
  - instantiate (2:=0); cbn. eauto.
  - cbv. auto.
Qed.

(** Gathering free names already used in the proofs *)
Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv_trm x) in
  let E := gather_vars_with (fun x : typ => fv_typ x) in
  let F := gather_vars_with (fun x : ctx => dom x) in
  constr:(A \u B \u C \u E \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.
Definition NAT := (typ_gadt [] Nat).
Definition const := trm_abs NAT (trm_abs NAT (#1)).
Lemma const_types : {natSigma, empty} ⊢ const ∈ (NAT ==> NAT ==> NAT).
  cbv.
  econstructor. introv xiL.
  econstructor. cbn.
  introv xiL0.
  Unshelve. 3: { exact \{x}. }
  econstructor.
  - auto.
  - econstructor; eauto.
    + econstructor; eauto.
      * econstructor; eauto.
      * econstructor; intuition.
    + econstructor; eauto.
      intuition.
Qed.

Definition const_test := (trm_app (trm_app const one) zero).
Lemma const_test_types : {natSigma, empty} ⊢ const_test ∈ NAT.
  cbv.
  econstructor.
  - apply zero_type.
  - econstructor.
    + apply one_type.
    + apply const_types.
Qed.

Inductive evals : trm -> trm -> Prop :=
| eval_step : forall a b c, a --> b -> evals b c -> evals a c
| eval_finish : forall a, evals a a.
Lemma const_test_evals : evals const_test one.
  cbv.
  eapply eval_step.
  - repeat econstructor; intuition.
  - eapply eval_step.
    + repeat econstructor; intuition.
    + cbv.
      apply eval_finish.
      Unshelve. fs. fs. fs.
Qed.


