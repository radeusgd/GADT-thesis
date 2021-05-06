Require Import TestCommon.
Require Import Equations.

Axiom Eq : var.

Open Scope L2GMu.
Axiom all_distinct : True.

(* De Bruijn indices for arguments are in 'reverse' order, that is the last arg on the list is treated as 'closest' and referred to as ##0 *)
Definition EqDef := (* Vector a len *)
  enum 2 {{
         (* refl : forall a, () -> Eq a a *)
         mkGADTconstructor 1 typ_unit [##0; ##0]*
         }}
.

Definition sigma :=
  empty
  & Eq ~ EqDef.

Definition Refl := (Eq, 0).

Lemma oksigma : okGadt sigma.
  unfold sigma.
  unfold EqDef.
  lets: is_var_defined_split.
  econstructor; autotyper1;
    try congruence;
    try econstructor; autotyper1;
      destruct_const_len_list;
      autotyper1.
Qed.

Definition coerce_typ : typ :=
  ∀ ∀ γ(##1, ##0) Eq ==> ##1 ==> ##0.

Definition coerce_trm : trm :=
  Λ (* A *) => Λ (* B *) =>
  λ (* eq: Eq A B *) γ(##1, ##0) Eq =>
  λ (* x : A *) ##1 =>
  case #1 (* eq *) as Eq of {
                   (* a' *) 1 (* _: unit *) => #1 (* x *)
                }.

Lemma coerce_types : {sigma, emptyΔ, empty} ⊢(Tgen) coerce_trm ∈ coerce_typ.
  cbv.
  lets: oksigma.
  eapply Tgen_from_any.
  autotyper3;
    rename x into u;
    rename x0 into A;
    rename x1 into B;
    rename x3 into x.
  rename v into α.
  forwards~ : H3 α.
  eapply typing_eq with (T1:=A).
  - autotyper4.
  - apply teq_transitivity with α.
    + apply teq_axiom. autotyper4.
    + apply teq_symmetry. apply teq_axiom. autotyper4.
  - autotyper4.
    Unshelve.
    fs.
    fs.
    fs.
Qed.

Definition transitivity_typ : typ :=
  ∀ ∀ ∀ γ(##2, ##1) Eq ==> γ(##1, ##0) Eq ==> γ(##2, ##0) Eq.

Definition transitivity_trm : trm :=
  Λ => Λ => Λ => λ γ(##2, ##1) Eq => λ γ(##1, ##0) Eq =>
  case #1 as Eq of {
                  1 =>
                  case #1 as Eq of {
                                  1 =>
                                  new Refl [| ##2 |] ( <.> )
                                }
                }
  .

Lemma transitivity_types : {sigma, emptyΔ, empty} ⊢(Tgen) transitivity_trm ∈ transitivity_typ.
  cbv.
  lets: oksigma.
  eapply Tgen_from_any.
  autotyper3;
    try solve [cbn in *; autotyper3].
  rename x0 into A.
  rename x1 into B.
  rename x2 into C.
  eapply Tgen_from_any.
  rename v into α.
  forwards~ : H3 α.
  autotyper4.
  rename v into β.
  forwards~ : H8 β.
  eapply typing_eq with (T1:= γ(typ_fvar C, typ_fvar C) Eq).
  - autotyper4.
  - apply eq_typ_gadt.
    apply F2_iff_In_zip.
    split~.
    intros T1 T2 In.
    repeat ininv2.
    + apply teq_reflexivity.
    + apply teq_transitivity with β.
      1: {
        apply teq_axiom. listin.
      }

      apply teq_transitivity with B.
      1: {
        apply teq_symmetry.
        apply teq_axiom. listin.
      }

      apply teq_transitivity with α.
      1: {
        apply teq_axiom. listin.
      }

      apply teq_symmetry.
      apply teq_axiom. listin.
  - autotyper4.
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
Qed.
