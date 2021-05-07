Require Import Helpers.
Require Import Library.
Require Import GMu.TestEquality.
Require Import Translation.

Definition p_coerce_typ : typ :=
  translateTyp0 coerce_typ.


Parameter refl : trm_label. (* TODO automatically generating constructor ids *)

Definition env_typ : typ :=
  μ
    { GN Eq ==
      μ
        {Bi 1 >: ⊥ <: ⊤}
      ∧ {Ai 1 == this ↓ Bi 1} ∧ {Ai 2 == this ↓ Bi 1}
      ∧ {data ⦂ super ↓ Unit }
    }
  ∧ { refl ⦂ ( ∀ ({Bi 1 >: ⊥ <: ⊤}) (super ↓ GN Eq) ∧ {Bi 1 == this ↓ Bi 1}) }
.

Definition env_trm : trm.
Admitted.

Lemma env_types : forall G,
    G ⊢ trm_let libTrm env_trm : env_typ ->
                                 G ⊢ trm_let libTrm env_trm : env_typ.
  intros.
Admitted.

(* lib and env cannot escape, but then we cannot really type the outer program... *)

(*
Definition coerce_trm : trm :=
  Λ (* A *) => Λ (* B *) =>
  λ (* eq: Eq A B *) γ(##1, ##0) Eq =>
  λ (* x : A *) ##1 =>
  case #1 (* eq *) as Eq of {
                   (* a' *) 1 (* _: unit *) => #1 (* x *)
                }.
 *)
Eval cbv in p_coerce_typ.
(*
     = ∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤}) (
         ∀ (((pvar env ↓ GN Eq) ∧ {Ai 1 == this ↓ GenT}) ∧ {Ai 2 == super ↓ GenT})
           (∀ (ssuper ↓ GenT) (ssuper ↓ GenT))))
     : typ
 *)

(* TODO: issue DeBruijn is not shared in L2GMu but is shared in pDOT! *)
Definition p_coerce_trm : trm :=
  λ ({GenT >: ⊥ <: ⊤}) λ ({GenT >: ⊥ <: ⊤})
    λ (((ssuper ↓ GN Eq) ∧ {Ai 1 >: ⊥ <: ⊤}) ∧ {Ai 2 >: ⊥ <: ⊤})
    λ (super ↓ GenT) trm_path this.

Lemma p_coerce_types :
    empty & lib ~ libType & env ~ env_typ ⊢
                            p_coerce_trm : p_coerce_typ.
  intros.
  cbv.
  crush.
  apply_fresh ty_all_intro as A; crush.
  apply_fresh ty_all_intro as B; crush.
  (* apply_fresh ty_all_intro as eq; crush. *)
  (* apply_fresh ty_all_intro as x; crush. *)
Admitted.

Definition p_transitivity_typ := translateTyp0 transitivity_typ.

Eval cbv in p_transitivity_typ.
