Require Import Helpers.
Require Import Library.
(*
*** Warning: in file Predefs.v,
    required library Definitions matches several files in path
    (found Definitions.v in ../lambda2Gmu and ../../dot-calculus/src/extensions/paths; used the latter)
 *)

Fixpoint translateType (T : Source.typ) (offset : nat) : Target.typ :=
  match T with
  | typ_bvar J =>
    typ_path (p_sel (avar_b J) nil) GenT
  | typ_fvar X =>
    typ_path (pvar X) GenT
  | typ_unit =>
    UnitT offset
  | T1 ** T2 =>
    let T1' := translateType T1 offset in
    let T2' := translateType T2 offset in
    TupleT offset T1' T2'
  | T1 ==> T2 =>
    let T1' := translateType T1 offset in
    let T2' := translateType T2 (1+offset) in
    typ_all T1' T2'
  | Source.typ_all T =>
    let T1 := translateType T (1+offset) in
    typ_all GenArgT T1
  | typ_gadt Ts g =>
    let Ts' := List.map (fun t => translateType t offset) Ts in
    let base := typ_path (p_sel (avar_b offset) nil) (GN g) in
    let res :=
        List.fold_left
          (fun acc T => match acc with
                     | (i, rest) =>
                       (
                         1+i,
                         (rest ∧ typ_rcd { Ai i >: ⊥ <: ⊤ })
                       )
                     end)
          Ts'
          (1, base) in
    snd res
  end.

Definition translateTyp0 (T : Source.typ) : Target.typ := translateType T 0.

Definition translateEnv (Σ : Source.GADTEnv) : Target.trm.
Admitted.

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
    typing Tgen Σ Δ E t T ->
    exists tt, forget tt = t /\ typinga Tgen Σ Δ E tt T.
Admitted.

Lemma forgetting_preserves_typing : forall Σ Δ E tt T,
    typinga Tgen Σ Δ E tt T ->
    typing Tgen Σ Δ E (forget tt) T.
Admitted.

Definition translation2 : forall Σ Δ E t T,
    typing Tgen Σ Δ E t T ->
    Target.trm.
  intros.
  induction t.
Admitted.

(* Lemma translation_correct : forall Σ Δ E t T, *)
(*     forall (TT : {Σ, Δ, E} ⊢(Tgen) t ∈ T), *)
(*       Target.ty_trm empty (translation2 Σ Δ E t T TT) (translateTyp0 T). *)
(* Admitted. *)

(* Lemma translation_same : forall Σ Δ E ta T, *)
(*     forall (TT : {Σ, Δ, E} ⊢(Tgen) (forget ta) ∈ T), *)
(*       translateProgram Σ ta = translation2 Σ Δ E (forget ta) T TT. *)
(* Admitted. *)

(* Lemma translation_set_correct : forall (), *)



(* lemma from https://stackoverflow.com/q/27322979/1296238 *)
Lemma ex_falso: forall T: Type, False -> T.
  inversion 1.
Qed.

(* Definition translator : translation_type. *)
(*   unfold translation_type. *)
(*   intro. *)
(*   induction t; introv; intros okGadt Htyp. *)
(*   - apply ex_falso. inversion Htyp. *)
(*   - apply ex_falso. inversion Htyp; subst. *)
(*     admit. *)
(*   - admit. *)
(*   - econstructor. *)
(* Admitted. *)
