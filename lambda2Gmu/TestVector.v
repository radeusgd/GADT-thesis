Require Import TestCommon.
Require Import Equations.

(*

This file implements a list type with type-level-encoded length, called Vector.

We introduce two phantom types: Zero : * and Succ : * -> *, to encode natural numbers on typelevel.

It has the following constructors:
data Vector A N
  empty : () -> Vector a Zero
  cons : (a * Vector a n) -> Vector a (Succ n)

or in dotty:
trait Zero
trait Succ[N]

enum Vector[A,N] {
  case Empty[A](unused: Unit) extends Vector[A, Zero]
  case Cons[A, N](data: (A, Vector[A, N])) extends Vector[A, Succ[N]]
}

Then we wrap the constructors as functions (just as an exercise):
  empty': forall a, Vector a Zero
  cons' : forall a n, a -> Vector a n -> Vector a (Succ n)
or in dotty:
  def empty[A]: Vector[A, Zero]
  def cons[A,N](head: A)(tail: Vector[A, N]): Vector[A, Succ[N]]

we can create a vector containing two units:
  uvec = (cons () (cons () empty)) // I skip the type args here, they are elaborated in the proof
  uvec : Vector Unit (Succ (Succ Zero))

we can create a map function that guarantees that it preserves length:
  map : forall a b n, (a -> b) -> Vector a n -> Vector b n

then we implement the 'safe' head function that works only on non-empty vectors:
  head : forall a n, Vector a (Succ n) -> a
  def head[A,N](v: Vector[A, Succ[N]]): A
this will be an occassion to show how we handle contradictory branches:
- we may use the contradictory type equalities to prove that unit: A for every a and just return it

another showcase of GADT abilities will be a typesafe zip function that only allows to zip vectors of equal length
  zip : forall a b n, Vector a n -> Vector b n -> Vector (a * b) n
  def zip[A,B,N](va: Vector[A,N])(vb: Vector[B,N]): Vector[(A,B), N]

  append (nat - plus)
*)

(* type level natural numbers *)
Axiom Zero : var.
Axiom Succ : var.
Axiom Vector : var.

Open Scope L2GMu.
Axiom all_distinct :
  (Zero <> Succ) /\ (Succ <> Vector) /\ (Zero <> Vector).

(* De Bruijn indices for arguments are in 'reverse' order, that is the last arg on the list is treated as 'closest' and referred to as ##0 *)
Definition VectorDef := (* Vector a len *)
  enum 2 {{
         (* empty : forall a, () -> Vector a Zero *)
         mkGADTconstructor 1 typ_unit [##0; γ() Zero]* |
         (* cons : forall a n, (a * Vector a n) -> Vector a (Succ n) *)
         mkGADTconstructor 2 (##1 ** γ(##1, ##0) Vector) [##1; γ(##0) Succ]*
         }}
.

Definition sigma :=
  empty
    (* Zero and Succ are phantom types, but we add them constructors as at least one constructor is required for consistency *)
  & Zero ~ enum 0 {{
           mkGADTconstructor 0 typ_unit []*
         }}
  & Succ ~ enum 1 {{
           mkGADTconstructor 1 typ_unit [##0]*
         }}
  & Vector ~ VectorDef.

Lemma oksigma : okGadt sigma.
Proof.
  unfold sigma.
  unfold VectorDef.
  lets [? [? ?]]: all_distinct.
  lets: is_var_defined_split.
  econstructor; autotyper1;
    try congruence;
    try econstructor; autotyper1;
      destruct_const_len_list;
      autotyper1;
      repeat rewrite union_empty_r; auto.
Qed.

Definition Nil := (Vector, 0).
Definition Cons := (Vector, 1).

Definition nil A := new Nil [| A |] (trm_unit).
Definition cons A N h t := new Cons [|A, N|]  (trm_tuple h t).

Lemma nil_type : {sigma, emptyΔ, empty} ⊢(Treg) (Λ => nil (##0)) ∈ typ_all (γ(##0, γ() Zero) Vector).
Proof.
  cbv.
  lets: oksigma.
  autotyper1.
Qed.

Ltac distinct22 :=
  lazymatch goal with
  | |- ?a <> ?b =>
    match goal with
    | H: a \in ?S -> False |- _ =>
      intro; apply H; subst; apply in_singleton_self
    | H: b \in ?S -> False |- _ =>
      intro; apply H; subst; apply in_singleton_self
    end
  end.

Ltac free_abs :=
  unshelve econstructor; cbv; try (let v := gather_vars in exact v).

Lemma notin_eqv : forall A (x : A) L,
    (x \in L -> False) <-> x \notin L.
Proof.
  introv.
  intuition.
Qed.

Lemma cons_type :
  {sigma, emptyΔ, empty} ⊢(Treg)
                         (Λ => Λ =>
                          (λ ##1 => λ γ(##1, ##0) Vector =>
                           cons (##1) (##0) (#1) (#0)
                         ))
                         ∈
                         ∀ ∀ (##1 ==> (γ(##1, ##0) Vector) ==> (γ(##1, γ(##0) Succ) Vector)).
Proof.
  cbv.
  lets: oksigma.
  autotyper1.
Qed.

Definition GZ := γ() Zero.
Definition GS (T : typ) := γ(T) Succ.

Definition uvec2 := cons typ_unit (GS GZ) trm_unit (cons typ_unit GZ trm_unit (nil typ_unit)).

Definition two := GS (GS GZ).
Lemma uvec2_type : {sigma, emptyΔ, empty} ⊢(Treg) uvec2 ∈ γ(typ_unit, two) Vector.
Proof.
  cbv.
  lets: oksigma.
  lets [? [? ?]]: all_distinct.
  autotyper1.
Qed.

(*
  map : forall a b n, (a -> b) -> Vector a n -> Vector b n
 *)
Definition map :=
  fixs ∀ ∀ ∀ ((##2 ==> ##1) ==> γ(##2, ##0) Vector ==> γ(##1, ##0) Vector) =>
  Λ (* a *) => Λ (* b *) => Λ (* n *) =>
  λ (* f *) (##2 ==> ##1) =>
  λ (* v *) γ(##2, ##0) Vector =>
  case #0 as Vector of {
                      (* a' *) 1 => new Nil [| ##2 |] ( <.> ) |
                      (* a', n'; elem *) 2 => new Cons [| ##3, ##0 |] (
                                      trm_tuple
                                        (#2 <| fst(#0))
                                        (#3 <|| ##4 <|| ##3 <|| ##0 <| #2 <| snd(#0))
                                    )
                    }.


Lemma map_types : {sigma, emptyΔ, empty} ⊢(Treg) map ∈ ∀ ∀ ∀ ((##2 ==> ##1) ==> γ(##2, ##0) Vector ==> γ(##1, ##0) Vector).
Proof.
  cbv.
  lets: oksigma.
  lets [? [? ?]]: all_distinct.
  autotyper3;
    rename x0 into map;
    rename x4 into f;
    rename x1 into A;
    rename x2 into B;
    rename x3 into N;
    rename x5 into vec.
  - rename v into C.
    forwards~ : H6 C.
    eapply typing_eq with (T1:=γ(typ_fvar B, γ() Zero) Vector).
    + autotyper4.
    + apply eq_typ_gadt.
      apply F2_iff_In_zip.
      split~.
      intros.
      repeat ininv2.
      * apply teq_symmetry.
        apply teq_axiom. listin.
      * apply teq_reflexivity.
    + autotyper4.
  - rename v0 into A'.
    rename v into N'.
    forwards~ : H6 A'.
    forwards~ : H6 N'.
    apply typing_eq with (γ(typ_fvar B, γ(typ_fvar N') Succ) Vector) Treg.
    + eapply typing_cons; autotyper0.
      * eapply typing_tuple; autotyper0.
        -- econstructor.
           ++ instantiate (1:=A).
              apply typing_eq with A' Treg.
              ** autotyper4.
              ** apply teq_symmetry. apply teq_axiom. listin.
              ** autotyper4.
           ++ autotyper4.
        -- econstructor; autotyper0.
           instantiate (1:= γ(typ_fvar A, typ_fvar N') Vector).
           ++ apply typing_eq with (γ(typ_fvar A', typ_fvar N') Vector) Treg.
              ** autotyper4.
              ** apply eq_typ_gadt.
                 apply F2_iff_In_zip.
                 split~.
                 intros.
                 repeat ininv2.
                 --- apply teq_reflexivity.
                 --- apply teq_symmetry.
                     apply teq_axiom. listin.
              ** autotyper4.
           ++ autotyper4.
      * autotyper4.
    + apply eq_typ_gadt.
      apply F2_iff_In_zip.
      split~.
      intros.
      repeat ininv2.
      * apply teq_symmetry.
        apply teq_axiom. listin.
      * apply teq_reflexivity.
    + autotyper4.
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
Qed.
