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
(* TODO Parameter *)
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
Axiom diff : Unit <> Tuple
             /\ mkUnit <> mkTuple
             /\ T1 <> T2
             /\ fst <> snd.
 (* This will become tedious... it would be good to materialize these identifiers somehow... *)

Require Import Lists.List.
Import ListNotations.
Require Import ExampleTactics.

Notation "'{' A '==' T '}'" := (dec_typ A T T).
Coercion typ_rcd : dec >-> Target.typ.
Notation "'{(' a , .. , c ')}'" := (defs_cons (.. (defs_cons defs_nil a) ..) c).
Coercion trm_val  : val >-> trm.
(* TODO not sure if this is not too many coercions... *)
Coercion defp : path >-> def_rhs.
Coercion defv : val >-> def_rhs.

Lemma intersection_order : forall G A1 B1 A2 B2,
    G ⊢ A1 <: A2 ->
              G ⊢ B1 <: B2 ->
                        G ⊢ A1 ∧ B1 <: A2 ∧ B2.
  intros.
  apply subtyp_and2.
  - apply subtyp_trans with A1; auto.
  - apply subtyp_trans with B1; auto.
Qed.

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
      { T1 >: ⊥ <: ⊤ } ∧
      { T2 >: ⊥ <: ⊤ } ∧
      { fst ⦂ typ_path (ref 0) T1 } ∧
      { snd ⦂ typ_path (ref 0) T2 }
    ).

Definition TupleT (offset : nat) (TT1 TT2 : Target.typ) : Target.typ :=
  (ref offset ↓ Tuple) ∧ { T1 == TT1 } ∧ { T2 == TT2 }.

Definition GenArgT : Target.typ :=
  typ_rcd { GenT >: ⊥ <: ⊤ }.

Definition libPreTypeHelp (unitDec : dec) : typ :=
  typ_rcd unitDec ∧
  typ_rcd { Tuple == tupleTyp } ∧
  typ_rcd { mkUnit ⦂ UnitT 0 } ∧
  typ_rcd { mkTuple ⦂
                    ∀ ({ T1 >: ⊥ <: ⊤} ∧ { T2 >: ⊥ <: ⊤ })
                        ∀ ((ref 0) ↓ T1)
                            ∀ ((ref 1) ↓ T2)
                              ((ref 3) ↓ Tuple ∧ { T1 == (ref 2) ↓ T1 } ∧ { T2 == (ref 2) ↓ T2 })
          }.

Definition libPreType : Target.typ :=
  libPreTypeHelp { Unit == { Unit >: ⊥ <: ⊤ } }.

Definition libType : Target.typ :=
  μ (libPreTypeHelp { Unit >: ⊥ <: ⊤ }).

Definition internalTupleTyp :=
  { T1 == (ref 3) ↓ T1 } ∧
  { T2 == (ref 3) ↓ T2 } ∧
  { fst ⦂ {{ ref 2 }} } ∧
  { snd ⦂ {{ ref 1 }} }.

Definition libInternalType (unitRef : path) :=
  typ_rcd { Unit == { Unit >: ⊥ <: ⊤ } } ∧
  typ_rcd { Tuple == tupleTyp } ∧
  typ_rcd { mkUnit ⦂ {{ unitRef }} } ∧
  typ_rcd { mkTuple ⦂
                    ∀ ({ T1 >: ⊥ <: ⊤} ∧ { T2 >: ⊥ <: ⊤ })
                        ∀ ((ref 0) ↓ T1)
                            ∀ ((ref 1) ↓ T2)
                              ((ref 3) ↓ Tuple ∧ { T1 == (ref 2) ↓ T1 } ∧ { T2 == (ref 2) ↓ T2 })
          }.

Definition libTrm : Target.trm :=
  trm_let
    (let_trm (ν({ Unit == ⊤ }) {( {Unit ⦂= ⊤} )}))
  (let_trm
    (ν(libInternalType (ref 1)) {(
                           { Unit ⦂= { Unit >: ⊥ <: ⊤ } },
                           { Tuple ⦂= tupleTyp },
                           { mkUnit := ref 1 },
                           { mkTuple :=
                               λ ({ T1 >: ⊥ <: ⊤} ∧ { T2 >: ⊥ <: ⊤ })
                                 λ ((ref 0) ↓ T1)
                                 λ ((ref 1) ↓ T2)
                                 let_trm (
                                   ν(internalTupleTyp)
                                    {(
                                        {T1 ⦂= (ref 3) ↓ T1},
                                        {T2 ⦂= (ref 3) ↓ T2},
                                        { fst := (ref 2) },
                                        { snd := (ref 1) }
                                    )}
                                 )
                           }
                        )}
    ))
 .

Lemma libTypes : forall G, G ⊢ libTrm : libType.
  intros.
  unfold libTrm. unfold libType.
  let F := gather_vars in
  apply ty_let with F ({ Unit >: ⊥ <: ⊤ }).
  1: {
    let F := gather_vars in
    apply ty_let with F (μ { Unit == ⊤ }).
    - apply_fresh ty_new_intro as u.
      crush.
    - intros u Fru.
      crush.
      apply ty_sub with {Unit == ⊤}.
      + assert (HU: typ_rcd {Unit == ⊤} = open_typ_p (pvar u) {Unit == ⊤}) by crush.
        rewrite HU.
        apply ty_rec_elim.
        apply~ ty_var.
      + apply~ subtyp_typ.
  }

  intros u Fru.
  crush.
  let F := gather_vars in
  apply ty_let with F (μ libInternalType (pvar u)).
  - cbv.
    apply_fresh ty_new_intro as z.
    crush.
    repeat apply ty_defs_cons; try apply ty_defs_one.
    + apply ty_def_typ.
    + apply ty_def_typ.
    + crush. destructs diff. false.
    + apply~ ty_def_path.
    + crush.
    + apply ty_def_all.
      apply_fresh ty_all_intro as tl.
      apply_fresh ty_all_intro as x1.
      apply_fresh ty_all_intro as x2.
      cbv. repeat case_if.
      clear - Frz Frtl Frx1 Frx2.
      eapply ty_let.
      * apply_fresh ty_new_intro as w.
        crush.
        repeat apply ty_defs_cons; try apply ty_defs_one;
          auto; try crush.
        -- inversion C. destructs diff. false.
        -- apply~ ty_def_path.
        -- apply~ ty_def_path.
        -- inversion C. destructs diff. false.
      * crush.
        let F := gather_vars in
        intros tup Frtup;
          instantiate (1:=F) in Frtup.
        repeat apply ty_and_intro.
        -- eapply ty_sub with (μ (({T1 >: ⊥ <: ⊤} ∧ {T2 >: ⊥ <: ⊤}) ∧ {fst ⦂ this ↓ T1}) ∧ {snd ⦂ this ↓ T2}).
           ++ apply ty_rec_intro.
              crush.
              repeat apply ty_and_intro.
              ** match goal with
                 | [ |- context[tup ~ μ ?T] ] =>
                   apply ty_sub with T
                 end.
                 --- match goal with
                     | [ |- ?G ⊢ tvar tup : ?T ] =>
                       assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                         rewrite Hre;
                         clear Hre
                     end.
                     apply ty_rec_elim. cbn. apply~ ty_var.
                 --- eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and11.
                     apply~ subtyp_typ.
              ** match goal with
                 | [ |- context[tup ~ μ ?T] ] =>
                   apply ty_sub with T
                 end.
                 --- match goal with
                     | [ |- ?G ⊢ tvar tup : ?T ] =>
                       assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                         rewrite Hre;
                         clear Hre
                     end.
                     apply ty_rec_elim. cbn. apply~ ty_var.
                 --- eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and11.
                     eapply subtyp_trans; try apply subtyp_and12.
                     apply~ subtyp_typ.
              ** apply ty_rcd_intro.
                 apply ty_sngl with (pvar x1).
                 --- apply ty_new_elim.
                     match goal with
                     | [ |- context[tup ~ μ ?T] ] =>
                       apply ty_sub with T
                     end.
                     +++ match goal with
                         | [ |- ?G ⊢ tvar tup : ?T ] =>
                           assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                             rewrite Hre;
                             clear Hre
                         end.
                         apply ty_rec_elim. cbn. apply~ ty_var.
                     +++ eapply subtyp_trans; try apply subtyp_and11.
                         eapply subtyp_trans; try apply subtyp_and12.
                         apply subtyp_refl.
                 --- apply ty_sub with (pvar tl ↓ T1).
                     +++ auto.
                     +++ eapply subtyp_sel2.
                         match goal with
                         | [ |- context[tup ~ μ ?T] ] =>
                           apply ty_sub with T
                         end.
                         *** match goal with
                             | [ |- ?G ⊢ tvar tup : ?T ] =>
                               assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                                 rewrite Hre;
                                 clear Hre
                             end.
                             apply ty_rec_elim. cbn. apply~ ty_var.
                         *** eapply subtyp_trans; try apply subtyp_and11.
                             eapply subtyp_trans; try apply subtyp_and11.
              ** apply ty_rcd_intro.
                 apply ty_sngl with (pvar x2).
                 --- apply ty_new_elim.
                     match goal with
                     | [ |- context[tup ~ μ ?T] ] =>
                       apply ty_sub with T
                     end.
                     +++ match goal with
                         | [ |- ?G ⊢ tvar tup : ?T ] =>
                           assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                             rewrite Hre;
                             clear Hre
                         end.
                         apply ty_rec_elim. cbn. apply~ ty_var.
                     +++ eapply subtyp_trans; try apply subtyp_and12.
                         apply subtyp_refl.
                 --- apply ty_sub with (pvar tl ↓ T2).
                     +++ auto.
                     +++ eapply subtyp_sel2.
                         match goal with
                         | [ |- context[tup ~ μ ?T] ] =>
                           apply ty_sub with T
                         end.
                         *** match goal with
                             | [ |- ?G ⊢ tvar tup : ?T ] =>
                               assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                                 rewrite Hre;
                                 clear Hre
                             end.
                             apply ty_rec_elim. cbn. apply~ ty_var.
                         *** eapply subtyp_trans; try apply subtyp_and11.
                             eapply subtyp_trans; try apply subtyp_and11.
                             eapply subtyp_trans; try apply subtyp_and12.
                             auto.
           ++ eapply subtyp_sel2.
              match goal with
              | [ |- context [z ~ ?T] ] =>
                apply ty_sub with T
              end.
              ** apply~ ty_var.
              ** eapply subtyp_trans; try apply subtyp_and11.
                 eapply subtyp_trans; try apply subtyp_and11.
                 apply subtyp_and12.
        -- apply ty_sub with (({T1 == pvar tl ↓ T1} ∧ {T2 == pvar tl ↓ T2}) ∧ {fst ⦂ {{pvar x1}}} ∧ {snd ⦂ {{pvar x2}}}).
           ++ match goal with
              | [ |- ?G ⊢ tvar tup : ?T ] =>
                assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                  rewrite Hre;
                  clear Hre
              end.
              apply ty_rec_elim.
              cbn in *.
              apply ty_var. auto.
           ++ repeat (eapply subtyp_trans; try apply subtyp_and11).
        -- apply ty_sub with (({T1 == pvar tl ↓ T1} ∧ {T2 == pvar tl ↓ T2}) ∧ {fst ⦂ {{pvar x1}}} ∧ {snd ⦂ {{pvar x2}}}).
           ++ match goal with
              | [ |- ?G ⊢ tvar tup : ?T ] =>
                assert (Hre: T = open_typ_p (pvar tup) T) by (cbn; auto);
                  rewrite Hre;
                  clear Hre
              end.
              apply ty_rec_elim.
              cbn in *.
              apply ty_var. auto.
           ++ eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and11.
              apply subtyp_and12.
    + crush.
      inversion C17. destructs diff. false.
  - intros x Frx.
    cbv. crush.
    apply ty_rec_intro.
    crush.
    repeat apply ty_and_intro.
    + match goal with
      | [ |- context [ x ~ (μ ?B) ] ] =>
        apply ty_sub with (open_typ_p (pvar x) B)
      end.
      * apply~ ty_rec_elim.
      * crush.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and11.
        apply~ subtyp_typ.
    + match goal with
      | [ |- context [ x ~ (μ ?B) ] ] =>
        apply ty_sub with (open_typ_p (pvar x) B)
      end.
      * apply~ ty_rec_elim.
      * crush.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and11.
        eapply subtyp_trans; try apply subtyp_and12.
        apply~ subtyp_refl.
    + apply ty_rcd_intro.
      apply ty_sngl with (pvar u).
      * apply ty_new_elim.
        match goal with
        | [ |- context [ x ~ (μ ?B) ] ] =>
          apply ty_sub with (open_typ_p (pvar x) B)
        end.
        -- apply~ ty_rec_elim.
        -- crush.
           eapply subtyp_trans; try apply subtyp_and11.
           eapply subtyp_trans; try apply subtyp_and12.
           apply subtyp_refl.
      * apply ty_sub with ({Unit >: ⊥ <: ⊤}).
        -- auto.
        -- eapply subtyp_sel2.
           match goal with
           | [ |- context [ x ~ (μ ?B) ] ] =>
             apply ty_sub with (open_typ_p (pvar x) B)
           end.
           ++ apply~ ty_rec_elim.
           ++ crush.
              eapply subtyp_trans; try apply subtyp_and11.
              eapply subtyp_trans; try apply subtyp_and11.
    + match goal with
      | [ |- context [ x ~ (μ ?B) ] ] =>
        apply ty_sub with (open_typ_p (pvar x) B)
      end.
      ++ apply~ ty_rec_elim.
      ++ crush.
Qed.

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
