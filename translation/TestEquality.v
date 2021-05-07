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
        {Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤}
      ∧ {pmatch ⦂ ∀ ({GenT >: ⊥ <: ⊤})
                      ∀ ( ∀ (ssuper ↓ GC Eq 0 ∧ {{super}} ) (this ↓ GenT))
                        (super ↓ GenT)
        }
    }
  ∧ { GC Eq 0 ==
      μ
        this ↓ GN Eq
      ∧ {Bi 1 >: ⊥ <: ⊤}
      ∧ {Ai 1 == this ↓ Bi 1} ∧ {Ai 2 == this ↓ Bi 1}
      ∧ {data ⦂ super ↓ Unit}
    }
  ∧ { refl ⦂ ( ∀ ({Bi 1 >: ⊥ <: ⊤}) (super ↓ GC Eq 0) ∧ {Bi 1 == this ↓ Bi 1}) }
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
    λ (((pvar env ↓ GN Eq) ∧ {Ai 1 == this ↓ GenT}) ∧ {Ai 2 == super ↓ GenT})
    λ (ssuper ↓ GenT)
    trm_let
    (let_trm (ν({GenT == sssuper ↓ GenT}) {( {GenT ⦂= sssuper ↓ GenT} )} ))
    (trm_let
       (λ (pvar env ↓ GC Eq 0 ∧ {{ssuper}}) trm_path ssuper)
       (trm_let
          (trm_app (sssuper • pmatch) super)
          (let_trm (trm_app this super))
       )
    )
    .

Lemma p_coerce_types :
    empty & lib ~ libType & env ~ env_typ ⊢
                                p_coerce_trm : p_coerce_typ.
  lets lib: lib.
  lets env: env.
  intros.
  cbv.
  crush.
  apply_fresh ty_all_intro as A; crush.
  apply_fresh ty_all_intro as B; crush.
  apply_fresh ty_all_intro as eq; crush.
  apply_fresh ty_all_intro as x; crush.
  apply_fresh ty_let as TL; crush.
  - instantiate (1:= {GenT == pvar B ↓ GenT}).
    apply_fresh ty_let as μt.
    + apply_fresh ty_new_intro as μs; crush.
    + crush.
      assert (HR: open_typ_p (pvar μt) {GenT == pvar B ↓ GenT} = {GenT == pvar B ↓ GenT}) by crush.
      rewrite <- HR at 2.
      apply ty_rec_elim. crush.
  - apply_fresh ty_let as c0case; crush.
    + admit.
    + apply_fresh ty_let as app_tmp1; crush.
      * admit.
      * apply_fresh ty_let as res_tmp.
        -- admit.
        -- admit.
        (* instantiate (1:= ∀ ( ∀ (pvar env ↓ GC Eq 0 ∧ {{pvar eq}} ) (pvar TL ↓ GenT) )
                        (pvar TL ↓ GenT)). *)
Admitted.

Definition p_transitivity_typ := translateTyp0 transitivity_typ.

Eval cbv in p_transitivity_typ.
