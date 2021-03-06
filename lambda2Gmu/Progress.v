Require Import Prelude.
Require Import Infrastructure.
Require Import Regularity.
Require Import CanonicalForms.
Require Import Equations.

#[export] Hint Resolve binds_empty_inv.

Ltac empty_binding :=
  match goal with
  | H: binds ?x ?v empty |- _ => apply binds_empty_inv in H; contradiction
  | _ => fail "no empty bindings found"
  end.

Ltac IHT e :=
  match goal with
  | Ht: {?Σ, ?D, ?E} ⊢(?TT) e ∈ ?T |- _ =>
    match goal with
    | IH: forall T, ?P0 -> {Σ, D, E} ⊢(?TT2) e ∈ T -> ?P |- _ =>
      let H := fresh "IHt" in
      assert P as H; eauto
    end
  end.

Ltac generalize_typings :=
  match goal with
  | [ H: {?Σ, ?D, ?E} ⊢(?TT) ?e ∈ ?T |- _ ] =>
    match TT with
    | Tgen => fail 1
    | Treg => fail 1
    | _ => apply Tgen_from_any in H
    end
  end.

#[export] Hint Constructors value red.
Theorem progress_thm : progress.
  unfold progress.
  introv Typ.
  assert (Hterm: term e).
  1: {
    eapply typing_implies_term; eauto.
  }
  apply Tgen_from_any in Typ. clear TT.

  gen T Hterm.
  induction e using trm_ind;
    introv TypGen Hterm;
    lets [T2 [TypReg EQ]]: inversion_typing_eq TypGen;
    inversion TypReg;
    inversion Hterm;
    subst;
    try solve [
          left*
        | repeat generalize_typings;
          forwards* [Hv1 | [e1' Hred1]]: IHe1;
          forwards* [Hv2 | [e2' Hred2]]: IHe2
        ]; clear TypGen EQ T; try rename T2 into T.
  - empty_binding.
  - admit.
  - generalize_typings.
    forwards * [Hval | [? ?]]: IHe.
    admit.
  -  Δ ⊢ t1 ≡ t2 /\ fv_typ t1 = ∅ , t2, Δ consistent -> t1 = t2

    inversion Hval; 
    right.
  - 
    + apply~ IHe.

    IHT e.
    destruct IHt as [ | Hred].
    + left*.
    + right.
      destruct Hred as [e' Hred].
      eexists. constructor*.
  (* - left*. *)
  (* - IHT e1; IHT e2. *)
  (*   destruct IHt as [IHv1 | IHev1]. *)
  (*   + destruct IHt0 as [IHv2 | IHev2]. *)
  (*     * left*. *)
  (*     * inversion IHev2 as [e2' Hev2]. *)
  (*       right*. *)
  (*   + inversion IHev1; right; eauto. *)
  (* - IHT e. *)
  (*   destruct IHt as [Hv | Hev]. *)
  (*   + copy Hv. *)
  (*     eapply CanonicalFormTuple in Hv; eauto. *)
  (*     inversion Hv as [v1 Hv2]; inversion Hv2 as [v2 Heq]; subst. *)
  (*     right*. *)

  (*   + inversion Hev as [e' ev]; eauto. *)
  (* - IHT e. *)
  (*   destruct IHt as [Hv | Hev]. *)
  (*   + copy Hv. *)
  (*     eapply CanonicalFormTuple in Hv; eauto. *)
  (*     inversion Hv as [v1 Hv2]; inversion Hv2 as [v2 Heq]; subst. *)
  (*     right*. *)
  (*   + inversion Hev as [e' ev]; eauto. *)
  (* - left; econstructor; econstructor; eauto. *)
  (* - IHT e1; IHT e2. *)
  (*   destruct IHt as [Hv1 | Hev1]. *)
  (*   + destruct IHt0 as [Hv2 | Hev2]. *)
  (*     * copy Hv1. *)
  (*       eapply CanonicalFormAbs in Hv1; eauto. *)
  (*       inversion Hv1 as [v1 Heq]; subst. *)
  (*       right; eexists; econstructor; eauto. *)
  (*     * right; inversion Hev2; eexists; eauto. *)
  (*   + right; inversion Hev1; eexists; eauto. *)
  (* - left; econstructor; econstructor; eauto. *)
  (* - IHT e. *)
  (*   destruct IHt as [Hv | Hev]. *)
  (*   + right. *)
  (*     eapply CanonicalFormTAbs in Hv; eauto. *)
  (*     inversion Hv as [v1 eq]; subst. *)
  (*     eexists. econstructor; eauto. *)
  (*   + right; inversion Hev; eauto. *)
  (* - right. *)
  (*   eexists. *)
  (*   constructor*. *)
  (* - right. *)
  (*   rename l into ms. *)
  (*   inversions Htyp. *)
  (*   lets* IHe2: IHe H2. *)
  (*   destruct IHe2 as [Hval | [e' Hred]]. *)
  (*   + lets* [GCargs [GCind [GCterm Heq]]]: CanonicalFormGadt H2. *)
  (*     subst. *)

  (*     match goal with *)
  (*     | [ H: {?A, ?B, ?C} ⊢ trm_constructor ?D ?E ?F ∈ ?G |- _ ] => *)
  (*       inversions H *)
  (*     end. *)
  (*     lets* bindeq: binds_ext H4 H6. *)
  (*     inversions bindeq. *)
  (*     lets* bindeq: binds_ext H4 H9. *)
  (*     inversions bindeq. *)

  (*     lets: nth_error_implies_zip. *)
  (*     match goal with *)
  (*     | [ Hnth: List.nth_error ?As ?i = Some ?A |- _ ] => *)
  (*       match goal with *)
  (*       | [ Hlen: length As = length ?Bs |- _ ] => *)
  (*         lets* [[clA clT] [nth_cl inzip]]: nth_error_implies_zip Hnth Hlen *)
  (*       end *)
  (*     end. *)
  (*     assert (clA = length GCargs). *)
  (*     * match goal with *)
  (*       | [ H: forall def clause, List.In (def, clause) ?A -> clauseArity clause = Carity def |- _ ] => *)
  (*         lets*: H inzip *)
  (*       end. *)
  (*     * subst. *)
  (*       eexists. *)
  (*       econstructor; eauto. *)
  (*   + eexists; eauto. *)
  (* - IHT e1. *)
  (*   right. destruct IHt as [Hv | Hev]. *)
  (*   + eexists. econstructor; eauto. *)
  (*   + inversion Hev as [e1' ev]. *)
  (*     eexists; eapply ered_let; eauto. *)

  (* - eapply typing_implies_term; eauto. *)
Admitted.
