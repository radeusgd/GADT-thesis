Require Import Definitions.
Require Import TLC.LibLN.

(* TODO merge with Tests.v *)

Notation "@ n" := (typ_bvar n) (at level 42).
Notation "# n" := (trm_bvar n) (at level 42).
Ltac fs := exact \{}. (* There must be a better way *)

Axiom Nat : var.
Definition NatDef := GADT 0 [
                            GADTconstr 0 typ_unit (typ_gadt [] Nat);
                            GADTconstr 0 (typ_gadt [] Nat) (typ_gadt [] Nat)
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
      * intros. destruct Alphas; inversions H; econstructor.
        intros.
        inversion H.
        auto. auto.
      * auto.
    + econstructor.
      * intros. destruct Alphas; inversions H; econstructor.
        intros.
        inversion H.
        auto. auto.
      * intros. destruct Alphas; inversions H; econstructor.
        intros.
        inversion H.
        auto. auto.
      * auto.
        Unshelve. fs. fs.
Qed.

Definition zero := trm_constructor [] (Nat, 0) trm_unit.

Lemma zero_type : {natSigma, empty} ⊢ zero ∈ typ_gadt [] Nat.
  cbv.
  econstructor; eauto.
  - cbn.
    instantiate (3:=0).
    cbn.
    eauto.
  - econstructor.
    econstructor. apply oknat.
  - cbv. eauto.
Qed.

Definition succ := trm_abs (typ_gadt [] Nat) (trm_constructor [] (Nat, 1) (#0)).

Lemma succ_type : {natSigma, empty} ⊢ succ ∈ (typ_gadt [] Nat) ==> (typ_gadt [] Nat).
  cbv.
  econstructor.
  intros.
  econstructor; eauto.
  - cbn. instantiate (3:=0); cbn. eauto.
  - cbv. case_if.
    econstructor; eauto.
    econstructor; eauto.
    econstructor. apply oknat.
    econstructor; eauto.
    intros. inversions H0.
  - cbn. auto.
Qed.
