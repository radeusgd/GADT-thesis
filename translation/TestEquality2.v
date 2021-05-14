Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
Require Import GMu.TestEquality.
Require Import Translation.
Require Import Top.TestEqualityEnv.

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
    (TLgen (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* B *) ref 3 ↓ GenT}) ∧ {Ai 2 == (* A *) ref 4 ↓ GenT}))
    (let_trm (
      (ref 1) • pmatch $ ref 0 $
              (λ (*eq1_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 1 }})
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
  remember lib as lib.
  remember env as env.
  intros.
  cbv.
  crush.
  apply_fresh ty_all_intro as A; crush.
  apply_fresh ty_all_intro as B; crush.
  apply_fresh ty_all_intro as C; crush.
  apply_fresh ty_all_intro as D; crush.
  cleanup.
  rewrite <- Heqlib.
  rewrite <- Heqenv.
  apply_fresh ty_all_intro as eq; crush.
  apply_fresh ty_let as TL.
  1: {
    apply_fresh ty_let as TLres.
    - apply_fresh ty_new_intro as TLself.
      crush.
    - cbn. case_if.
      match goal with
      | [ |- context [ TLres ~ μ ?T ] ] =>
        instantiate (1:=T);
          assert (HR: T = open_typ_p (pvar TLres) T) by crush;
          rewrite HR;
          clear HR
      end.
      apply ty_rec_elim; crush.
  }
  crush.

  apply_fresh ty_let as res.
  - apply_fresh ty_let as app_tmp1.
    + eapply ty_all_elim.
      * fold ((pvar eq) • pmatch).
        apply ty_new_elim.
        instantiate (1:=(∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{pvar eq}})
                              (super ↓ GenT)) (super ↓ GenT))).
        instantiate (1:={GenT >: ⊥ <: ⊤}).
        cleanup.
        match goal with
        | [ |- context [{GN Eq == μ ?T}] ] =>
          apply ty_sub with (open_typ_p (pvar eq) (open_rec_typ_p 1 (pvar env) T))
        end.
        -- apply ty_rec_elim. crush.
           apply ty_sub with (pvar env ↓ GN Eq).
           ++ var_subtyp2.
              solve_subtyp_and.
           ++ subsel1.
              var_subtyp_mu2.
              solve_subtyp_and.
        -- crush.
      * var_subtyp2.
        auto.
    + crush.
      apply_fresh ty_let as case0.
      * apply_fresh ty_all_intro as eq_ev.
        instantiate (1:=(pvar TL ↓ GenT)).
        crush.
        cleanup.
        apply_fresh ty_let as BTL.
        1: {
          apply_fresh ty_let as BTLtmp.
          - apply_fresh ty_new_intro as BTLself.
            crush.
          - instantiate (1:={Bi 1 == pvar B ↓ GenT}).
            crush. var_subtyp_mu2.
        }

        crush. cleanup.
        apply_fresh ty_let as res.
        -- eapply ty_all_elim.
           fold ((pvar env) • refl).
           apply ty_new_elim.
           var_subtyp_mu2.
           var_subtyp2.
           apply subtyp_typ; auto.
        -- crush.

           match goal with
           | [ |- ?GG ⊢ ?t : ?T ] =>
             remember GG as G
           end.

           assert (EB: G ⊢ pvar BTL ↓ Bi 1 =:= pvar B ↓ GenT).
           1: {
             constructor;
             [ subsel1 | subsel2 ];
             rewrite HeqG;
             auto.
           }

           assert (G ⊢ pvar A ↓ GenT =:= pvar B ↓ GenT).
           1: {
             admit.
           }

           assert (EA: G ⊢ pvar BTL ↓ Bi 1 =:= pvar A ↓ GenT).
           1: {
             apply eq_transitive with (pvar B ↓ GenT);
             auto using eq_symmetry.
           }

           rewrite HeqG.
           var_subtyp2.
           subsel2.
           var_subtyp2.
           rewrite <- HeqG.
           destruct EA; destruct EB.
           apply subtyp_typ;
             repeat apply intersection_order; auto.
      * crush.
        cleanup.
        instantiate (1:=(pvar TL ↓ GenT)).
        assert (HR: (pvar TL ↓ GenT) = open_typ_p (pvar case0) (pvar TL ↓ GenT)) by crush.
        rewrite HR.
        eapply ty_all_elim; crush.
  - crush. cleanup.
    var_subtyp2.
    subsel1.
    apply ty_var; solve_bind.
Admitted.
