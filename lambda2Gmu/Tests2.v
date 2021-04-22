Require Import TestCommon.

Open Scope L2GMu.
Axiom Nat : var.
Definition NatDef :=
  enum 0 {{
             mkGADTconstructor 0 typ_unit []*
             |
             mkGADTconstructor 0 (γ() Nat) []*
         }}.

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

Definition zero := new (Nat, 0) [| |] (trm_unit).

Lemma zero_type : {natSigma, emptyΔ, empty} ⊢(Treg) zero ∈ γ() Nat.
  cbv.
  lets: oknat.
  autotyper1.
Qed.

Require Import Psatz.
Definition one := new (Nat, 1) [| |] (zero).
Lemma one_type : {natSigma, emptyΔ, empty} ⊢(Treg) one ∈ γ() Nat.
  cbv.
  lets: oknat.
  autotyper1.
Qed.

Definition succ := λ γ() Nat => (new (Nat, 1) [| |] (#0)).

Lemma succ_type : {natSigma, emptyΔ, empty} ⊢(Treg) succ ∈ (γ() Nat) ==> (γ() Nat).
  cbv.
  lets: oknat.
  autotyper1.
Qed.

Definition const := λ γ() Nat => (λ γ() Nat => #1).
Lemma const_types : {natSigma, emptyΔ, empty} ⊢(Treg) const ∈ (γ() Nat ==> γ() Nat ==> γ() Nat).
  cbv.
  lets: oknat.
  autotyper1.
Qed.

Definition const_test := const <| one <| zero.
Lemma const_test_types : {natSigma, emptyΔ, empty} ⊢(Treg) const_test ∈ γ() Nat.
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

Definition plus :=
  trm_fix
    ((typ_gadt []* Nat) ==> ((typ_gadt []* Nat) ==> (typ_gadt []* Nat)))
    (trm_abs
       (typ_gadt []* Nat)
       (trm_abs
          (typ_gadt []* Nat)
          (trm_matchgadt
             (#1)
             Nat
             [
               clause 0 (trm_app (trm_app (#3) (#0)) (trm_constructor []* (Nat, 1) (#1)));
             clause 0 (#1)
             ]*
    ))).


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

Ltac clauseDefResolver1 :=
  match goal with
  | [ H: (?A, ?B) = (?C, ?D) |- _ ] =>
    inversions H; cbn in *; autotyper1
  end.

Ltac fresh_intros := let free := gather_vars in
  let x' := fresh "x" in
  let xiL := fresh "xiL" in
  intros x' xiL; intros;
    try instantiate (1 := free) in xiL.

Lemma plus_types : {natSigma, emptyΔ, empty} ⊢(Treg) plus ∈ ((typ_gadt []* Nat) ==> ((typ_gadt []* Nat) ==> (typ_gadt []* Nat))).
  cbv.
  lets: oknat.
  econstructor.
  1: autotyper1; cbn in *; destruct_const_len_list; autotyper1.
  intros x Fr. clear Fr.
  econstructor; cbn in *.
  fresh_intros.
  econstructor.
  fresh_intros.
  econstructor; cbn in *; eauto.
  autotyper1.
  autotyper1.
  inversions H0. cbn. auto.
  inversions H0. cbn. auto.
  let free := gather_vars in
  intros;
    try instantiate (1 := free) in H4.
  inversions H0.
  - inversions H6. cbn in *.
    destruct_const_len_list. cbn.
    autotyper1.
  - inversions H6.
    + inversions H0.
      destruct_const_len_list. cbn.
      autotyper1.
    + cbn in *. false.
    Unshelve.
    fs.
Qed.

Ltac destruct_clauses :=
  repeat match goal with
         | [ H: clause ?A ?B = ?cl \/ ?X |- _ ] =>
           destruct H
         end.

Definition two := trm_constructor []* (Nat, 1) one.
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
