Require Import TestCommon.

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

>> ^ this is implemented
>> the things below are not (yet) because pattern matching is not yet done and they require it

we can create a map function that guarantees that it preserves length:
  map : forall a b n, (a -> b) -> Vector a n -> Vector b n

then we implement the 'safe' head function that works only on non-empty vectors:
  head : forall a n, Vector a (Succ n) -> a
  def head[A,N](v: Vector[A, Succ[N]]): A
this will be an occassion to show how we handle contradictory branches:
- (TODO this is a draft) we may try to use the contradictory type equalities to prove that unit: A for every a and just return it
  we will later try to show that contradictory branches are never actually executed

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
Definition VectorDef := (* Vector a len *)
  enum 2 {{
         (* empty : () -> Vector a Zero *)
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

Definition nil A := new (Vector, 0) [| A |] (trm_unit).
Definition cons A N h t := new (Vector, 1) [|A, N|]  (trm_tuple h t).

Lemma nil_type : {sigma, emptyΔ, empty} ⊢(Treg) (Λ => nil (##0)) ∈ typ_all (γ(##0, γ() Zero) Vector).
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
  cbv.
  lets: oksigma.
  autotyper1.
Qed.

Definition GZ := γ() Zero.
Definition GS (T : typ) := γ(T) Succ.

Definition uvec2 := cons typ_unit (GS GZ) trm_unit (cons typ_unit GZ trm_unit (nil typ_unit)).

Definition two := GS (GS GZ).
Lemma uvec2_type : {sigma, emptyΔ, empty} ⊢(Treg) uvec2 ∈ γ(typ_unit, two) Vector.
  cbv.
  lets: oksigma.
  lets [? [? ?]]: all_distinct.
  autotyper1.
Qed.
