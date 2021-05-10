Require Import Helpers.
Require Import Library.
Require Import TestHelpers.
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


Definition make_fun_apply (f : trm) (arg : trm) : trm :=
  match f with
  | trm_path pf =>
    match arg with
    | trm_path pa =>
      trm_app pf pa
    | _ =>
      trm_let arg (trm_app (shift1_p pf) this)
    end
  | _ =>
    trm_let
      f
      (trm_let (shift1_trm arg)
               (trm_app super this)
      )
  end.

Notation "f $ a" := (make_fun_apply f a) (at level 42).

Definition TLgen (T : typ) : trm :=
  let inner := shift1_typ T in
  let_trm (ν({GenT == inner}) {( {GenT ⦂= inner} )}).

Section TestApp.
  Definition a := trm_path this.
  Definition b := trm_path super.
  Definition c := trm_path ssuper.

  Axiom A B C : var.

  Definition sub (t : trm) : trm :=
    open_rec_trm_p 2 (pvar C) (open_rec_trm_p 1 (pvar B) (open_trm_p (pvar A) t)).

  Goal sub b = tvar B.
    cbv. crush.
  Qed.
  Goal sub a = tvar A.
    cbv. crush.
  Qed.
  Goal sub c = tvar C.
    cbv. crush.
  Qed.

  Definition t :=
    a $ b $ c.

  Goal sub t = tvar A $ tvar B $ tvar C.
    cbv.
    crush.
  Qed.

  Eval cbv in tvar A $ tvar B $ tvar C.
End TestApp.

Definition p_coerce_trm : trm :=
  λ ({GenT >: ⊥ <: ⊤}) λ ({GenT >: ⊥ <: ⊤})
    λ (((pvar env ↓ GN Eq) ∧ {Ai 1 == this ↓ GenT}) ∧ {Ai 2 == super ↓ GenT})
    λ (ssuper ↓ GenT)
    trm_let
    (TLgen (ref 2 ↓ GenT))
    (trm_path ssuper • pmatch $ trm_path this $ (λ (pvar env ↓ GC Eq 0 ∧ {{ssuper}}) trm_path ssuper)).

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
    apply_fresh ty_let as app_tmp1; crush.
    + instantiate (1:= open_typ_p (pvar TL) (∀ ( ∀ (pvar env ↓ GC Eq 0 ∧ {{pvar eq}} ) (super ↓ GenT) ) (super ↓ GenT))).

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
    + apply_fresh ty_let as c0case; crush.
      1: {
        instantiate (1:= ∀ (pvar env ↓ GC Eq 0 ∧ {{pvar eq}} ) (pvar TL ↓ GenT) ).
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
                apply ty_var. solve_bind.
             ++ apply subtyp_trans with (pvar eq_ev ↓ Ai 2).
                ** eapply subtyp_sngl_qp with (p := pvar eq_ev) (q := pvar eq);
                     try solve [var_subtyp; crush; apply ty_var; solve_bind].
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
                     try solve [var_subtyp; crush; apply ty_var; solve_bind].
                   assert (HR: pvar eq_ev = (pvar eq_ev) •• []) by crush.
                   rewrite HR at 2.
                   assert (HR2: pvar eq = (pvar eq) •• []) by crush.
                   rewrite HR2 at 2.
                   apply rpath.
             ++ eapply subtyp_sel1.
                var_subtyp; crush; try (apply ty_var; solve_bind).
                eapply subtyp_trans; try apply subtyp_and11.
                apply subtyp_and12.
      }

crush.
      apply ty_sub with (pvar TL ↓ GenT); crush.
      * assert (HR: open_typ_p (pvar c0case) (pvar TL ↓ GenT) = pvar TL ↓ GenT) by crush.
        rewrite <- HR.
        eapply ty_all_elim; crush.
      * crush.
        eapply subtyp_sel1.
        crush.
Qed.

Definition p_transitivity_typ : typ := translateTyp0 transitivity_typ.

Eval cbv in p_transitivity_typ.
(*
     = ∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤}) (∀ ({GenT >: ⊥ <: ⊤})
        (∀ (((pvar env ↓ GN Eq) ∧ {Ai 1 == super ↓ GenT}) ∧ {Ai 2 == ssuper ↓ GenT})
         (∀ (((pvar env ↓ GN Eq) ∧ {Ai 1 == super ↓ GenT}) ∧ {Ai 2 == ssuper ↓ GenT})
           (((pvar env ↓ GN Eq) ∧ {Ai 1 == ssuper ↓ GenT}) ∧ {Ai 2 == ssssuper ↓ GenT})))))
     : Target.typ
 *)

Coercion trm_path : path >-> trm.

Definition p_transitivity_trm : trm :=
  λ (*A*) ({GenT >: ⊥ <: ⊤}) λ (*B*) ({GenT >: ⊥ <: ⊤}) λ (*C*) ({GenT >: ⊥ <: ⊤})
    λ (*eq1*) (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* B *) ref 1 ↓ GenT}) ∧ {Ai 2 == (* A *) ref 2 ↓ GenT})
    λ (*eq2*) (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* C *) ref 1 ↓ GenT}) ∧ {Ai 2 == (* B *) ref 2 ↓ GenT})
    trm_let
    (* TL = *)
    (TLgen (((pvar env ↓ GN Eq) ∧ {Ai 1 == (* C *) ref 2 ↓ GenT}) ∧ {Ai 2 == (* A *) ref 4 ↓ GenT}))
    (let_trm (
      (ref 2) • pmatch $ ref 0 $
              (λ (*eq1_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 2 }})
                 (ref 2) • pmatch $ ref 1 $
                 (λ (*eq2_ev *) (pvar env ↓ GC Eq 0 ∧ {{ ref 2 }})
                    (let_trm
                       ((pvar env) • refl $ (ν({Bi 1 == ref 6 ↓ GenT}) {( {Bi 1 ⦂= ref 6 ↓ GenT} )} ))
                    )
                 )
              )
    ))
.

Lemma p_transitivity_types :
  empty & lib ~ libType
  & env ~ (open_typ_p (pvar lib) env_typ)
        ⊢
        p_transitivity_trm : p_transitivity_typ.
  remember lib as lib.
  remember env as env.
  intros.
  cbv.
  crush.
  apply_fresh ty_all_intro as A; crush.
  apply_fresh ty_all_intro as B; crush.
  cleanup.
  apply_fresh ty_all_intro as C; crush.
  apply_fresh ty_all_intro as eq1; crush.
  apply_fresh ty_all_intro as eq2; crush.
  apply_fresh ty_let as TL; crush.
  1: {
    instantiate (1:= {GenT == (pvar env ↓ GN Eq) ∧ {Ai 1 == pvar C ↓ GenT} ∧ {Ai 2 == (pvar A) ↓ GenT } }).
    apply_fresh ty_let as TLlet.
    - apply_fresh ty_new_intro as TLself; crush.
    - crush.
      match goal with
      | [ |- ?G ⊢ ?t : ?T ] =>
        assert (HR: open_typ_p (pvar TLlet) T = T) by crush;
          rewrite <- HR;
          clear HR
      end.
      apply ty_rec_elim.
      rewrite <- Heqenv.
      apply ty_var.
      solve_bind.
  }

  apply_fresh ty_let as res.
  - apply_fresh ty_let as e1app1; crush.
    1: {
      eapply ty_all_elim.
      - assert (HR: p_sel (avar_f eq1) [pmatch] = (pvar eq1) • pmatch) by crush.
        rewrite HR.
        apply ty_new_elim.
        apply ty_sub with (open_typ_p (pvar eq1) (({Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤})
                                                 ∧ {pmatch
                                                      ⦂ ∀ ({GenT >: ⊥ <: ⊤}) (∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{super}})
                                                                                   (super ↓ GenT)) (super ↓ GenT) ) })).
        + apply ty_rec_elim.
          apply ty_sub with (pvar env ↓ GN Eq).
          * var_subtyp; crush.
            repeat rewrite <- Heqenv.
            eapply subtyp_trans; apply subtyp_and11.
          * eapply subtyp_sel1.
            match goal with
            | [ |- context [ env ~ μ ?T ] ] =>
              apply ty_sub with (open_typ_p (pvar env) T)
            end.
            -- apply ty_rec_elim. apply ty_var.
               solve_bind.
            -- crush.
               eapply subtyp_trans; try apply subtyp_and11.
        + crush.
      - eapply ty_sub.
        + apply ty_var. solve_bind.
        + apply~ subtyp_typ.
    }

    crush.
    apply_fresh ty_let as case1.
    + match goal with
      | [ |- context [ e1app1 ~ ∀ (?A) ?B ] ] =>
        instantiate (1:=A)
      end.
      rewrite <- Heqenv.
      apply_fresh ty_all_intro as eq_ev1.
      crush.
      apply_fresh ty_let as e2app1.
      1: {
        eapply ty_all_elim.
        - assert (HR: p_sel (avar_f eq2) [pmatch] = (pvar eq2) • pmatch) by crush.
          rewrite HR.
          apply ty_new_elim.
          apply ty_sub with (open_typ_p (pvar eq2) (({Ai 1 >: ⊥ <: ⊤} ∧ {Ai 2 >: ⊥ <: ⊤})
                                                    ∧ {pmatch
                                                         ⦂ ∀ ({GenT >: ⊥ <: ⊤}) (∀ (∀ ((pvar env ↓ GC Eq 0) ∧ {{super}})
                                                                                      (super ↓ GenT)) (super ↓ GenT) ) })).
          + apply ty_rec_elim.
            apply ty_sub with (pvar env ↓ GN Eq).
            * var_subtyp; crush.
              repeat rewrite <- Heqenv.
              eapply subtyp_trans; apply subtyp_and11.
            * eapply subtyp_sel1.
              match goal with
              | [ |- context [ env ~ μ ?T ] ] =>
                apply ty_sub with (open_typ_p (pvar env) T)
              end.
              -- apply ty_rec_elim. apply ty_var.
                 solve_bind.
              -- crush.
                 eapply subtyp_trans; try apply subtyp_and11.
          + crush.
        - eapply ty_sub.
          + apply ty_var. solve_bind.
          + apply~ subtyp_typ.
      }

      crush.
      apply_fresh ty_let as case2.
      * match goal with
        | [ |- context [ e2app1 ~ ∀ (?A) ?B ] ] =>
          instantiate (1:=A)
        end.
        apply_fresh ty_all_intro as eq_ev2.
        crush.
        admit.
      * crush.
        match goal with
        | [ |- ?G ⊢ ?e : ?T ] =>
          assert (HR: T = open_typ_p (pvar case2) T) by crush;
            rewrite HR;
            clear HR
        end.
        eapply ty_all_elim;
          apply ty_var; solve_bind.
    + crush.
      match goal with
      | [ |- context [ e1app1 ~ ∀ (?A) ?B ] ] =>
        instantiate (1:=B)
      end.
      match goal with
      | [ |- ?G ⊢ ?e : ?T ] =>
        assert (HR: T = open_typ_p (pvar case1) T) by crush;
          rewrite HR;
          clear HR
      end.
      eapply ty_all_elim;
        apply ty_var; solve_bind.
  - crush.
    eapply ty_sub.
    + apply ty_var; solve_bind.
    + eapply subtyp_sel1.
      rewrite <- Heqenv.
      crush.
Admitted.
