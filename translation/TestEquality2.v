Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
Require Import GMu.TestEquality.
Require Import Translation.
Require Import Top.TestEqualityEnv.
Require Import Top.TestEquality.

Definition p_destruct_typ : typ :=
  translateTyp0 destruct_typ.

Eval cbv in p_destruct_typ.
(*
  = ∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤})
    (∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤})
     (∀ (((pvar env ↓ GN Eq) ∧
           {Ai 1 == ((pvar lib ↓ Tuple) ∧ {T1 == ssuper ↓ GenT}) ∧ {T2 == this ↓ GenT}})
         ∧ {Ai 2 == ((pvar lib ↓ Tuple) ∧ {T1 == sssuper ↓ GenT}) ∧ {T2 == super ↓ GenT}})
      (((pvar env ↓ GN Eq) ∧ {Ai 1 == sssuper ↓ GenT}) ∧ {Ai 2 == ssssuper ↓ GenT})))))
     : typ
*)

Definition p_destruct_trm : trm :=
  λ (*A*) ({GenT >: ⊥ <: ⊤}) λ (*B*) ({GenT >: ⊥ <: ⊤})
    λ (*C*) ({GenT >: ⊥ <: ⊤}) λ (*D*) ({GenT >: ⊥ <: ⊤})
    λ (*eq1*) (((pvar env ↓ GN Eq) ∧
           {Ai 1 == ((pvar lib ↓ Tuple) ∧ {T1 == ssuper ↓ GenT}) ∧ {T2 == this ↓ GenT} })
         ∧ {Ai 2 == ((pvar lib ↓ Tuple) ∧ {T1 == sssuper ↓ GenT}) ∧ {T2 == super ↓ GenT} })
    trm_let
    (* TL = *)
    (TLgen (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* B *) ref 4 ↓ GenT}) ∧ {Ai 2 == (* A *) ref 5 ↓ GenT}))
    (let_trm (
      (ref 2) • pmatch $ ref 0 $
              (λ (*eq1_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 2 }})
                 ((pvar env) • refl $$ (let_trm (ν({Bi 1 == ref 6 ↓ GenT}) {( {Bi 1 ⦂= ref 6 ↓ GenT} )} )))
              )
    ))
.

Lemma p_destruct_types :
  empty & lib ~ libType
  & env ~ (open_typ_p (pvar lib) env_typ)
        ⊢
        p_destruct_trm : p_destruct_typ.
  (* TODO pDOT destruct Tuple EQ *)
Admitted.
