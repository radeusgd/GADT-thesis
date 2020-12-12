Require Import TestCommon.

Axiom Nat : var.
Definition NatDef := mkGADT 0 [
                            mkGADTconstructor 0 typ_unit [];
                            mkGADTconstructor 0 (typ_gadt [] Nat) []
                          ].

Definition natSigma := (empty & Nat ~ NatDef).

Lemma oknat : okGadt natSigma.
  unfold natSigma; unfold NatDef.
  constructor*.
  - intros.
    binds_inv.
    inversions EQ.
    splits*; try congruence.
    intros.
    repeat ininv.
    + econstructor; cbn; eauto; try solve [intros; intuition].
      intros.
      destruct_const_len_list. cbn. econstructor.
    + econstructor; cbn; eauto; try solve [intros; intuition].
      intros.
      destruct_const_len_list; cbn; econstructor; eauto.
      intros.
      contradiction.
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
  - cbv. intros. contradiction.
  - cbv. f_equal.
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
    + intros; contradiction.
  - cbn; f_equal.
    instantiate (2:=0). eauto.
  - intros; contradiction.
  - cbv; f_equal.
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
  - intros. contradiction.
  - cbv. auto.
Qed.

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
        apply oknat.
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

Definition plus := trm_fix ((typ_gadt [] Nat) ==> ((typ_gadt [] Nat) ==> (typ_gadt [] Nat))) (trm_abs (typ_gadt [] Nat) (trm_abs (typ_gadt [] Nat) (trm_matchgadt (#1) Nat [clause 0 (#1); clause 0 (trm_app (trm_app (#3) (#0)) (trm_constructor [] (Nat, 1) (#1)))]))).

Lemma plus_types : {natSigma, empty} ⊢ plus ∈ ((typ_gadt [] Nat) ==> ((typ_gadt [] Nat) ==> (typ_gadt [] Nat))).
  cbv.
  admit.
Admitted.

Definition two := trm_constructor [] (Nat, 1) one.
Lemma plus_evals : evals (trm_app (trm_app plus one) one) two.
  cbv.
  eapply eval_step.
Admitted.
