Require Import Predefs.
Require Import TLC.LibTactics.
Require Import TLC.LibLN.
Require Import GMu.Prelude.
Require Import Definitions.

(*
*** Warning: in file Predefs.v, 
    required library Definitions matches several files in path
    (found Definitions.v in ../lambda2Gmu and ../../dot-calculus/src/extensions/paths; used the latter)
*)

(* TODO can we instantiate this? Or maybe we don't need to? *)
Axiom Unit : typ_label.
Axiom Tuple : typ_label.
Axiom GenT : typ_label.
Axiom Ai : nat -> typ_label.
Axiom Bi : nat -> typ_label.
Axiom T1 : typ_label.
Axiom T2 : typ_label.
Axiom fst : trm_label.
Axiom snd : trm_label.
Axiom GN : Source.GADTName -> typ_label.
Axiom mkTuple : trm_label.
Axiom mkUnit : trm_label.

Definition refLibTyp (name : typ_label) (offset : nat) : Target.typ.
  apply typ_path.
  - constructor.
    + apply avar_b. exact offset.
    + apply nil.
  - exact name.
Defined.

Definition UnitT (offset : nat) : Target.typ :=
  refLibTyp Unit offset.

Definition ref (offset : nat) : path :=
  p_sel (avar_b offset) nil.

Definition tupleTyp : Target.typ :=
  μ (
      typ_rcd { T1 >: ⊥ <: ⊤ }
      ∧
      typ_rcd { T2 >: ⊥ <: ⊤ }
      ∧
      typ_rcd { fst ⦂ typ_path (ref 0) T1 }
      ∧
      typ_rcd { snd ⦂ typ_path (ref 0) T2 }
    ).

Definition TupleT (offset : nat) (T1 T2 : Target.typ) : Target.typ.
Admitted.

Definition GenArgT : Target.typ :=
  typ_rcd { GenT >: ⊥ <: ⊤ }.

Notation "'{' A '==' T '}'" := (dec_typ A T T).
Coercion typ_rcd : dec >-> Target.typ.
Notation "'{(' a , .. , c ')}'" := (defs_cons (.. (defs_cons defs_nil c) ..) a).
Coercion trm_val  : val >-> trm.
(* TODO not sure if this is not too many coercions... *)
Coercion defp : path >-> def_rhs.
Coercion defv : val >-> def_rhs.

Definition libPreType : Target.typ :=
      typ_rcd { Unit >: ⊥ <: ⊤ }
      ∧
      typ_rcd { Tuple >: tupleTyp <: tupleTyp }
      ∧
      typ_rcd { mkUnit ⦂ UnitT 0 }
      ∧
      typ_rcd { mkTuple ⦂
                        ∀ ({ T1 >: ⊥ <: ⊤} ∧ { T2 >: ⊥ <: ⊤ })
                            ∀ ((ref 0) ↓ T1)
                                ∀ ((ref 1) ↓ T1)
                                  ((ref 3) ↓ Tuple ∧ { T1 == (ref 2) ↓ T1 } ∧ { T2 == (ref 2) ↓ T2 })
              }.

Definition libType : Target.typ :=
  μ libPreType.

Definition libTrm : Target.trm :=
  ν(libPreType) {(
                 { Unit ⦂= { Unit >: ⊥ <: ⊤ } }, (* TODO maybe diff name... *)
                 { Tuple ⦂= tupleTyp },
                 { mkUnit := ν({ Unit >: ⊥ <: ⊤ }) {( {Unit ⦂= ⊤} )} },
                 { mkTuple := ν({ Unit >: ⊥ <: ⊤ }) {( {Unit ⦂= ⊤} )} }
             )}.

Lemma libTypes : forall G, G ⊢ libTrm : libType.
  intros.
  unfold libTrm. unfold libType.
  apply_fresh ty_new_intro as z.
  cbn. repeat case_if.
Admitted.

Fixpoint translateType (T : Source.typ) (offset : nat) : Target.typ.
  destruct T as []eqn:H.
  - (* bvar *)
    apply typ_path.
    + constructor.
      * exact (avar_b n).
      * exact nil.
    + apply GenT.
  - (* fvar *)
    exact (typ_path (pvar v) GenT).
  - (* unit *)
    exact (UnitT offset).
  - (* tuple *)
    refine (let T1 := translateType t1 offset in _).
    refine (let T2 := translateType t2 offset in _).
    exact (TupleT offset T1 T2).
  - (* ==> *)
    refine (let T1 := translateType t1 offset in _).
    refine (let T2 := translateType t2 (1+offset) in _).
    exact (typ_all T1 T2).
  - (* forall *)
    refine (let T1 := translateType t (1+offset) in _).
    exact (typ_all GenArgT T1).
  - (* GADT *)
    refine (let Ts := List.map (fun t => translateType t offset) l in _).
    refine (let base := typ_path (p_sel (avar_b offset) nil) (GN g) in _).
    refine (let Ts2 :=
                List.fold_left
                  (fun acc T => match acc with
                             | (i, rest) =>
                               (
                                 1+i,
                                 (rest ∧ typ_rcd { Ai i >: ⊥ <: ⊤ })
                               )
                             end)
                  Ts
                  (1, base)
            in _).
    destruct Ts2 as []eqn:Heq.
    exact t.
Defined.

Definition translateTyp0 (T : Source.typ) : Target.typ := translateType T 0.

Definition translateEnv (Σ : Source.GADTEnv) : Target.trm.
Admitted.

Axiom envId : var. (* TODO? *)

Inductive TypedTrm : Set :=. (*TODO*)

Fixpoint translateTerm (Σ : Source.GADTEnv) (typenv : list Target.typ) (trmenv : list Target.trm) (t : TypedTrm) : Target.trm.
Admitted.

Definition translateProgram (Σ : Source.GADTEnv) (main : TypedTrm) : Target.trm.
Admitted.

Fixpoint forget (t : TypedTrm) : Source.trm.
Admitted.

Import Source.
Axiom typinga : typing_taint -> GADTEnv -> typctx -> ctx -> TypedTrm -> typ -> Prop.
Definition typ_from_trm (tt : TypedTrm) : typ.
Admitted.

Lemma typing_gives_types : forall Σ Δ E t T,
    {Σ, Δ, E} ⊢(Tgen) t ∈ T ->
    exists tt, forget tt = t /\ typinga Tgen Σ Δ E tt T.
Admitted.

Lemma forgetting_preserves_typing : forall Σ Δ E tt T,
    typinga Tgen Σ Δ E tt T ->
    typing Tgen Σ Δ E (forget tt) T.
Admitted.

Definition translation2 : forall Σ Δ E t T,
    {Σ, Δ, E} ⊢(Tgen) t ∈ T ->
    Target.trm.
  intros.
  induction t.
Admitted.

Lemma translation_correct : forall Σ Δ E t T,
    forall (TT : {Σ, Δ, E} ⊢(Tgen) t ∈ T),
      Target.ty_trm empty (translation2 Σ Δ E t T TT) (translateTyp0 T).
Admitted.

Lemma translation_same : forall Σ Δ E ta T,
    forall (TT : {Σ, Δ, E} ⊢(Tgen) (forget ta) ∈ T),
      translateProgram Σ ta = translation2 Σ Δ E (forget ta) T TT.
Admitted.

Lemma translation_set_correct : forall (),



(* lemma from https://stackoverflow.com/q/27322979/1296238 *)
Lemma ex_falso: forall T: Type, False -> T.
  inversion 1.
Qed.

Definition translator : translation_type.
  unfold translation_type.
  intro.
  induction t; introv; intros okGadt Htyp.
  - apply ex_falso. inversion Htyp.
  - apply ex_falso. inversion Htyp; subst.
    admit.
  - admit.
  - econstructor.
Admitted.
