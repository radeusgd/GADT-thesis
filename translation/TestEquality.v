Require Import Helpers.
Require Import Library.
Require Import GMu.TestEquality.
Require Import Translation.

Definition p_coerce_typ : typ :=
  translateTyp0 coerce_typ.


Parameter refl : trm_label. (* TODO automatically generating constructor ids *)

Definition env_typ : typ :=
  μ (
      { GN Eq ==
        μ
          {Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤}
        ∧ {pmatch ⦂ ∀ ({GenT >: ⊥ <: ⊤})
                        ∀ ( ∀ (ssuper ↓ GC Eq 0 ∧ {{super}} ) (super ↓ GenT))
                          (super ↓ GenT)
          }
      }
      ∧ { GC Eq 0 ==
          μ
            super ↓ GN Eq
          ∧ {Bi 1 >: ⊥ <: ⊤}
          ∧ {Ai 1 == this ↓ Bi 1} ∧ {Ai 2 == this ↓ Bi 1}
          ∧ {data ⦂ ssuper ↓ Unit}
        }
      ∧ { refl ⦂ ( ∀ ({Bi 1 >: ⊥ <: ⊤}) (super ↓ GC Eq 0) ∧ {Bi 1 == this ↓ Bi 1}) }
    )
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

Ltac cleanup :=
  repeat
    match goal with
    | [ H: ?x <> ?y |- _ ] => clear H
    | [ H: ?x = ?y |- _ ] =>
      match x with
      | y => clear H
      end
    end.

Ltac var_subtyp :=
  match goal with
  | [ |- ?G ⊢ tvar ?x : ?T ] =>
    match goal with
    | [ |- context [x ~ ?BT] ] =>
      apply ty_sub with BT
    end
  end.

Ltac solve_bind :=
  repeat progress (
           lazymatch goal with
           | |- binds ?Var ?What (?Left & ?Right) =>
    match goal with
    | |- binds Var What (Left & Var ~ ?Sth) =>
      apply* binds_concat_right; apply* binds_single_eq
    | _ => apply* binds_concat_left
    end
           end).

Lemma p_coerce_types :
  empty & lib ~ libType
  & env ~ (open_typ_p (pvar lib) env_typ)
        ⊢
        p_coerce_trm : p_coerce_typ.
  remember lib as lib.
  remember env as env.
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
  - cleanup.
    apply_fresh ty_let as c0case; crush.
    + instantiate (1:= ∀ (pvar env ↓ GC Eq 0 ∧ {{pvar eq}} ) (pvar TL ↓ GenT) ).
      repeat rewrite <- Heqenv.
      apply_fresh ty_all_intro as eq_ev; crush.
      apply ty_sub with (pvar A ↓ GenT).
      * apply ty_var. crush.
      * apply subtyp_trans with (pvar B ↓ GenT).
        2: {
          eapply subtyp_sel2.
          crush.
        }
        apply subtyp_trans with (pvar eq_ev ↓ Bi 1).
        -- apply subtyp_trans with (pvar eq ↓ Ai 2).
           ++ eapply subtyp_sel2.
              var_subtyp; crush.
           ++ apply subtyp_trans with (pvar eq_ev ↓ Ai 2).
              ** eapply subtyp_sngl_qp with (p := pvar eq_ev) (q := pvar eq);
                   try solve [var_subtyp; crush].
                 assert (HR: pvar eq_ev = (pvar eq_ev) •• []) by crush.
                 rewrite HR at 2.
                 assert (HR2: pvar eq = (pvar eq) •• []) by crush.
                 rewrite HR2 at 2.
                 apply rpath.
              ** eapply subtyp_sel1.
                 apply ty_sub with (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}).
                 ---
                   assert (HR:
                             ((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1})
                              ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}
                                      =
                                      open_typ_p (pvar eq_ev) (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == this ↓ Bi 1}) ∧ {Ai 2 == this ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})) by crush.
                   rewrite HR.
                   apply ty_rec_elim.
                   apply ty_sub with (pvar env ↓ GC Eq 0).
                   +++ var_subtyp; crush.
                   +++ eapply subtyp_sel1.
                       match goal with
                       | [ |- context [ env ~ μ ?T ] ] =>
                         apply ty_sub with (open_typ_p (pvar env) T)
                       end.
                       *** apply ty_rec_elim. apply ty_var.
                           solve_bind.
                       *** crush.
                           eapply subtyp_trans; try apply subtyp_and11.
                           apply subtyp_and12.
                 --- eapply subtyp_trans; try apply subtyp_and11.
                     apply subtyp_and12.
        -- apply subtyp_trans with (pvar eq ↓ Ai 1).
           ++ apply subtyp_trans with (pvar eq_ev ↓ Ai 1).
              ** eapply subtyp_sel2.
                 apply ty_sub with (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1}) ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}).
                 ---
                   assert (HR:
                             ((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == pvar eq_ev ↓ Bi 1})
                              ∧ {Ai 2 == pvar eq_ev ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit}
                                      =
                                      open_typ_p (pvar eq_ev) (((((pvar env ↓ GN Eq) ∧ {Bi 1 >: ⊥ <: ⊤}) ∧ {Ai 1 == this ↓ Bi 1}) ∧ {Ai 2 == this ↓ Bi 1}) ∧ {data ⦂ pvar lib ↓ Unit})) by crush.
                   rewrite HR.
                   apply ty_rec_elim.
                   apply ty_sub with (pvar env ↓ GC Eq 0).
                   +++ var_subtyp; crush.
                   +++ eapply subtyp_sel1.
                       match goal with
                       | [ |- context [ env ~ μ ?T ] ] =>
                         apply ty_sub with (open_typ_p (pvar env) T)
                       end.
                       *** apply ty_rec_elim. apply ty_var.
                           solve_bind.
                       *** crush.
                           eapply subtyp_trans; try apply subtyp_and11.
                           apply subtyp_and12.
                 --- eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and11.
                     apply subtyp_and12.
              ** eapply subtyp_sngl_pq with (p := pvar eq_ev) (q := pvar eq);
                   try solve [var_subtyp; crush].
                 assert (HR: pvar eq_ev = (pvar eq_ev) •• []) by crush.
                 rewrite HR at 2.
                 assert (HR2: pvar eq = (pvar eq) •• []) by crush.
                 rewrite HR2 at 2.
                 apply rpath.
           ++ eapply subtyp_sel1.
              var_subtyp; crush.
              eapply subtyp_trans; try apply subtyp_and11.
              apply subtyp_and12.
    + apply_fresh ty_let as app_tmp1; crush.
      * instantiate (1:= open_typ_p (pvar TL) (∀ ( ∀ (pvar env ↓ GC Eq 0 ∧ {{pvar eq}} ) (super ↓ GenT) ) (super ↓ GenT))).
        eapply ty_all_elim.
        2: {
          apply ty_var. crush.
        }
        assert (HR: p_sel (avar_f eq) [pmatch] = (pvar eq) • pmatch) by crush.
        rewrite HR.

        match goal with
        | [ |- ?G ⊢ ?t : ∀ (?T) ?U ] =>
          apply ty_sub with (∀ ({GenT >: ⊥ <: ⊤}) U)
        end.
        --
          apply ty_new_elim.
          apply ty_sub with (open_typ_p (pvar eq) (({Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤})
        ∧ {pmatch
          ⦂ ∀ ({GenT >: ⊥ <: ⊤}) (∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{super}})
                                       (super ↓ GenT)) (super ↓ GenT) ) })).
          ++ apply ty_rec_elim.
             apply ty_sub with (pvar env ↓ GN Eq).
             ** var_subtyp; crush.
                repeat rewrite <- Heqenv.
                eapply subtyp_trans; apply subtyp_and11.
             ** eapply subtyp_sel1.
                match goal with
                | [ |- context [ env ~ μ ?T ] ] =>
                  apply ty_sub with (open_typ_p (pvar env) T)
                end.
                *** apply ty_rec_elim. apply ty_var.
                    solve_bind.
                *** crush.
                    eapply subtyp_trans; try apply subtyp_and11.
          ++ crush.
        -- apply_fresh subtyp_all as TLL; crush.
      * apply_fresh ty_let as res_tmp.
        -- crush.
           instantiate (1 := open_typ_p (pvar c0case) (pvar TL ↓ GenT)).
           eapply ty_all_elim; crush.
        -- crush.
           apply ty_sub with (pvar TL ↓ GenT); crush.
           eapply subtyp_sel1.
           crush.
Qed.

Definition p_transitivity_typ := translateTyp0 transitivity_typ.

Eval cbv in p_transitivity_typ.
