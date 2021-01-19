Require Import TestCommon.

Axiom Nat : var.
Definition NatDef := mkGADT 0 [
                            mkGADTconstructor 0 typ_unit [];
                            mkGADTconstructor 0 (typ_gadt [] Nat) []
                          ].

Definition natSigma := (empty & Nat ~ NatDef).
Lemma all_distinct : True.
  trivial.
Qed.

Lemma oknat : okGadt natSigma.
  unfold natSigma.
  unfold NatDef.
  econstructor;
    autotyper1;
    try congruence;
    try econstructor; autotyper1;
      destruct_const_len_list;
      autotyper1.
Qed.

#[export] Hint Immediate oknat.

Definition zero := trm_constructor [] (Nat, 0) trm_unit.

Lemma zero_type : {natSigma, emptyΔ, empty} ⊢ zero ∈ typ_gadt [] Nat.
  cbv.
  lets: oknat.
  autotyper1.
Qed.

Require Import Psatz.
Definition one := trm_constructor [] (Nat, 1) zero.
Lemma one_type : {natSigma, emptyΔ, empty} ⊢ one ∈ typ_gadt [] Nat.
  cbv.
  lets: oknat.
  autotyper1.
Qed.

Definition succ := trm_abs (typ_gadt [] Nat) (trm_constructor [] (Nat, 1) (#0)).

Lemma succ_type : {natSigma, emptyΔ, empty} ⊢ succ ∈ (typ_gadt [] Nat) ==> (typ_gadt [] Nat).
  cbv.
  autotyper1.
  apply oknat.
Qed.

Definition NAT := (typ_gadt [] Nat).
Definition const := trm_abs NAT (trm_abs NAT (#1)).
Lemma const_types : {natSigma, emptyΔ, empty} ⊢ const ∈ (NAT ==> NAT ==> NAT).
  cbv.
  autotyper1.
  apply oknat.
Qed.

Definition const_test := (trm_app (trm_app const one) zero).
Lemma const_test_types : {natSigma, emptyΔ, empty} ⊢ const_test ∈ NAT.
  cbv.
  lets: oknat.
  autotyper1.
Qed.


Ltac simpl_op := cbn; try case_if; auto.
Ltac crush_eval := repeat (try (apply eval_finish; eauto);
                           try (eapply eval_step; eauto);
                           autotyper1;
                           try econstructor;
                           simpl_op).
Lemma const_test_evals : evals const_test one.
  cbv.
  crush_eval.
Qed.

Definition plus := trm_fix ((typ_gadt [] Nat) ==> ((typ_gadt [] Nat) ==> (typ_gadt [] Nat))) (trm_abs (typ_gadt [] Nat) (trm_abs (typ_gadt [] Nat) (trm_matchgadt (#1) Nat [clause 0 (#1); clause 0 (trm_app (trm_app (#3) (#0)) (trm_constructor [] (Nat, 1) (#1)))]))).


Ltac autodestruct :=
  match goal with
  | [ H: ?A \/ ?B |- _ ] => destruct H
  | [ H: ?A /\ ?B |- _ ] => destruct H
  | [ H: (?a,?b) = (?c,?d) |- _ ] => inversions* H
  end.

Ltac instFresh H FV :=
  instantiate (1:=FV) in H.

Tactic Notation "with_fresh" tactic(act) :=
  let FV := gather_vars in
  act;
  (try match goal with
       | [ H: ?x \notin ?F |- _ ] =>
         instFresh H FV
       end).

Ltac crush_1 :=
  repeat (
      with_fresh (
          auto using oknat;
          econstructor)
    );
    try solve [
          intros; cbn in *; repeat autodestruct; contradiction
        | solve_dom all_distinct
        | binds_inv; congruence
        | cbn in *; solve_bind; try solve_dom all_distinct
        ].

Ltac clauseDefResolver1 :=
  match goal with
  | [ H: (?A, ?B) = (?C, ?D) |- _ ] =>
    inversions H; cbn in *; autotyper1
  end.

Lemma plus_types : {natSigma, emptyΔ, empty} ⊢ plus ∈ ((typ_gadt [] Nat) ==> ((typ_gadt [] Nat) ==> (typ_gadt [] Nat))).
  cbv.
  lets: oknat.
  autotyper1;
    cbn in *;
    (* let fr := gather_vars in *)
    destruct_const_len_list;
    autotyper1.
  - inversions H0.
    cbn. trivial.
  - inversions H0.
    cbn. trivial.
  - inversions H0.
    cbn.
    instantiate (1:= \{ x0 } \u \{ x1 } \u \{ x2 }) in H4.
    autotyper1.
  - inversions H0.
    cbn in *.
    congruence.
  - inversions H0.
    cbn.
    autotyper1.
  - inversions H0. cbn in *.
    congruence.
    Unshelve.
    fs.
Qed.

Ltac destruct_clauses :=
  repeat match goal with
         | [ H: clause ?A ?B = ?cl \/ ?X |- _ ] =>
           destruct H
         end.

Definition two := trm_constructor [] (Nat, 1) one.
Lemma plus_evals : evals (trm_app (trm_app plus one) one) two.
  cbv.
  crush_eval;
    repeat (
        cbn in *;
        destruct_const_len_list;
        autotyper1).
  Unshelve.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
  fs.
Qed.
