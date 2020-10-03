Require Import Definitions.
Require Import Infrastructure.
Require Import Psatz.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.

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
*)

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
    | H2: ~ List.In ?v ?L1 |- _ =>
      cbn in H2; eauto
    end
  end.

Ltac solve_bind_core :=
  lazymatch goal with
  | |- binds ?Var ?What (?Left & ?Right) =>
    match goal with
    | |- binds Var What (Left & Var ~ ?Sth) =>
      apply* binds_concat_right; apply* binds_single_eq
    | _ => apply* binds_concat_left
    end
  end.

Ltac solve_bind :=
  (repeat solve_bind_core); try (solve_dom).

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
           ++ solve_bind.
           ++ cbn; eauto.
    + econstructor.
      * intros. destruct_const_len_list. econstructor; cbn; econstructor; eauto.
        -- solve_bind. distinct2.
        -- intros.
           repeat ininv.
           ++ econstructor. solve_bind.
              distinct2.
           ++ econstructor.
              solve_bind.
      * intros. destruct_const_len_list.
        repeat ininv.
        -- cbn. econstructor.
           solve_bind; distinct2.
        -- cbn.
           econstructor.
           ++ intros; repeat ininv.
              econstructor. solve_bind.
           ++ solve_bind.
           ++ cbn. eauto.
        Unshelve. fs. fs.
Qed.

Definition nil A := trm_constructor [A] (Vector, 0) trm_unit.
Definition cons A N h t := trm_constructor [A; N] (Vector, 1) (trm_tuple h t).

Lemma nil_type : {sigma, empty} ⊢ (trm_tabs (nil (@0))) ∈ typ_all (typ_gadt [@0; typ_gadt [] Zero] Vector).
  cbv.
  econstructor.
  - introv xiL.
    repeat econstructor; cbv.
    introv Heq.
    repeat destruct Heq as [Heq | Heq];
      subst; try econstructor; contradiction.
  - introv xiL.
    repeat (try apply oksigma; econstructor); cbn.
    + solve_dom.
    + solve_bind.
    + cbv.
      f_equal.
    + cbn. auto.
      Unshelve. fs.
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

Lemma cons_type : {sigma, empty} ⊢ (trm_tabs (trm_tabs (trm_abs (@1) (trm_abs (typ_gadt [@1; @0] Vector) (cons (@1) (@0) (#1) (#0)))))) ∈ typ_all (typ_all (typ_arrow (@1) (typ_arrow (typ_gadt [@1; @0] Vector) (typ_gadt [@1; typ_gadt [@0] Succ] Vector)))).
  cbv.
  econstructor.
  - introv XiL.
    repeat econstructor; cbv;
      introv Heq; repeat destruct Heq as [Heq | Heq];
        subst; try econstructor; contradiction.
  - introv XiL.
    free_abs.
    + introv X0iX.
      repeat econstructor;
        introv Heq; repeat destruct Heq as [Heq | Heq];
          subst; try econstructor; contradiction.
    + introv X0iX.
      free_abs.
      introv xiL.
      free_abs.
      introv xix.
      (repeat (try apply oksigma; econstructor); solve_bind);
        try solve [
              rewrite notin_eqv in *; eauto
            | cbv; auto
            | introv LiT;
              repeat destruct LiT as [LiT | LiT]; subst;
              solve [
                  contradiction
                | econstructor; solve_bind; rewrite notin_eqv in *; eauto
                ]
            ].
      Unshelve. fs. fs. fs. fs. fs. fs. fs. fs.
Qed.

Definition GZ := typ_gadt [] Zero.
Definition GS (T : typ) := typ_gadt [T] Succ.

Definition uvec2 := cons typ_unit (GS GZ) trm_unit (cons typ_unit GZ trm_unit (nil typ_unit)).

Lemma uvec2_type : {sigma, empty} ⊢ uvec2 ∈ typ_gadt [typ_unit; GS (GS GZ)] Vector.
  cbv.
  econstructor; eauto.
  2: {
    cbn. f_equal.
  }
  - cbv.
    repeat ((try apply oksigma); eauto; econstructor).
  - cbv. f_equal.
Qed.
