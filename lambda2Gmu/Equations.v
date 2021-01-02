Require Import TLC.LibLN.
Require Import Definitions.
Require Import TLC.LibTactics.
Require Import List.
Import List.ListNotations.

(*
This file is a work in progress.
It tries to prove that the original definition of semantic entailment of type equalities is equivalent with a simpler definition where order of equations and variables does not matter.
The latter might be easier for usage in proofs, but I decided to pause proving this equivalence until I really actually need it.
*)

Section TypCtxDefEquivalence.
  (* Here we present the typctx defined precisely as in the paper and show that these two notions are essentially equivalent *)

Record typctx' : Type := mkΔ {
                           Δvars : fset var;
                           Δeqs : fset type_equation
                         }.

Definition add_var' (Δ : typctx') (A : var) : typctx' :=
  mkΔ (\{A} \u Δvars Δ) (Δeqs Δ).
Definition add_eq' (Δ : typctx') (eq : type_equation) : typctx' :=
  mkΔ (Δvars Δ) (\{eq} \u Δeqs Δ).
Definition emptyΔ' := mkΔ \{} \{}.

Fixpoint translate (Δ : typctx) : typctx' :=
  match Δ with
  | [] => emptyΔ'
  | (tc_var A) :: Δt => add_var' (translate Δt) A
  | (tc_eq eq) :: Δt => add_eq'  (translate Δt) eq
  end.

Definition subst_matches_typctx' Σ Δ Θ :=
  substitution_sources Θ = Δvars Δ /\
  (forall A T, In (A,T) Θ -> wft Σ emptyΔ T) /\
  (forall T1 T2, (T1 ≡ T2) \in (Δeqs Δ) ->
            alpha_equivalent (subst_tt' T1 Θ) (subst_tt' T2 Θ)).

(* Lemma wft_strengthen_var : forall T Σ Δ A, *)
(*     wft Σ Δ T -> *)
(*     wft Σ (add_var Δ A) T. *)
(*   induction 1; econstructor; eauto. *)
(*   - destruct Δ as [vars ?]. *)
(*     cbn in *. *)
(*     rewrite in_union. right*. *)
(*   - intros. *)
(*     assert (Hcom: add_var (add_var Δ A) X = add_var (add_var Δ X) A). *)
(*     + cbv. f_equal. *)
(*       rewrite union_assoc. *)
(*       rewrite (union_comm \{X} \{A}). *)
(*       rewrite <- union_assoc. *)
(*       trivial. *)
(*     + rewrite Hcom. apply H0. eauto. *)
(* Qed. *)

(* Lemma subst_extend: *)
(*   forall (Θ : list (var * typ)) A (T T1 T2 : typ), *)
(*     subst_tt' T1 Θ = subst_tt' T2 Θ -> *)
(*     subst_tt' (subst_tt A T T1) Θ = subst_tt' (subst_tt A T T2) Θ. *)
(* Proof. *)
(*   induction Θ as [| (X, U) Θ]; introv IHC. *)
(*   - cbn in *. subst. trivial. *)
(*   - cbn. cbn in IHC. *)
(*     apply IHΘ. *)
(*     rewrite  subst_hmm. *)

(* Lemma subst_reverse : forall Θ T1 T2 A U, *)
(*   subst_tt A U (subst_tt' T1 Θ) = subst_tt A U (subst_tt' T2 Θ) -> *)
(*   subst_tt' (subst_tt A U T1) Θ = subst_tt' (subst_tt A U T2) Θ. *)
(*   induction Θ as [| (X, V) Θ]; introv IHC. *)
(*   - cbn in *. auto. *)
(*   - cbn in *. *)
(*     lets HA: subst_hmm T1 T2 X A V. *)
(*     lets HB: HA U. *)
(*     lets IH: IHΘ (subst_tt A U T1) (subst_tt A U T2) X V. *)
(*     apply IH. *)
(*     f_equal. *)
(*     apply IHΘ. *)
(* Abort. *)

Definition entails_semantic' Σ (Δ' : typctx') (eq : type_equation) :=
  match eq with
  | T1 ≡ T2 =>
    forall Θ, subst_matches_typctx' Σ Δ' Θ ->
         alpha_equivalent (subst_tt' T1 Θ) (subst_tt' T2 Θ)
  end.

Lemma empty_concat_inv : forall A (x : A) B,
    \{} = \{x} \u B -> False.
  intros.
  assert (Hf: x \in \{}).
  -- rewrite H.
     rewrite in_union. left. rewrite in_singleton. trivial.
  -- rewrite in_empty in Hf. trivial.
Qed.

(* Theorem subst_equivalence : forall Δ' Σ Δ, *)
(*     okGadt Σ -> *)
(*     translate Δ' = Δ -> *)
(*     forall Θ, *)
(*     subst_matches_typctx' Σ Δ' Θ <-> subst_matches_typctx Σ Δ Θ *)
(*     . *)
(*   induction Δ'; introv HokΣ Htranslate. *)
(*   - cbn in Htranslate. subst. *)
(*     intuition. *)
(*     + inversions H. *)
(*       unfold subst_matches_typctx. *)
(*       splits*. *)
(*       * intros; contradiction. *)
(*       * intros. *)
(*         cbv in H. rewrite in_empty in H. contradiction. *)
(*     + destruct H as [? [? ?]]. *)
(*       cbn in *. *)
(*       destruct Θ. *)
(*       * econstructor. *)
(*       * exfalso. *)
(*         cbn in H. *)
(*         apply* empty_concat_inv. *)
(*   - destruct a; cbn in Htranslate. *)
(*     + constructor; introv Hsm; subst. *)
(*       * admit. *)
(*       * destruct Hsm as [Hsrc [Hwft Haeq]]. *)
(*         destruct Θ as [| (X,V) Θ']. *)
(*         -- cbn in Hsrc. *)
(*            exfalso; apply* empty_concat_inv. *)
(*         -- assert (X = A). *)
(*            ++ admit. *)
(*            ++ subst. apply tc_add_var. *)
(*               ** apply wft_strengthen_var. *)


(*       * constructor; intro H. *)
(*         -- inversion H. *)
(*         -- inversion H as [? [? ?]]. *)
(*            destruct Δ as [vars ?]. *)
(*            cbn in *. *)
(*            subst. *)
(*            inversion Htranslate. *)
(*            assert (Hf: A \in \{}). *)
(*            ++ rewrite <- H3. *)
(*               rewrite in_union. left. rewrite in_singleton. trivial. *)
(*            ++ rewrite in_empty in Hf; contradiction. *)
    (*   * lets* [IH1 IH2]: IHΔ' Θ' Σ (translate Δ'). *)
    (*     intuition. *)
    (*     -- inversions H. *)
    (*        lets [IHA [IHB IHC]]: IH1 H6. *)
    (*        unfold subst_matches_typctx. *)
    (*        splits*. *)
    (*        ++ cbn. rewrite <- IHA. auto. *)
    (*        ++ introv Hin. *)
    (*           destruct Hin. *)
    (*           ** inversions H. *)
    (*              apply* wft_strengthen_var. *)
    (*           ** apply* wft_strengthen_var. *)
    (*        ++ introv Hin. *)
    (*           unfold alpha_equivalent in *. *)
    (*           cbn in Hin. *)
    (*           cbn. *)
    (*           admit. *)
    (*     -- admit. *)
    (* + constructor; intro H. *)
    (*   * admit. *)
    (*   * admit. *)

Theorem equivalence : forall Δ' Δ,
    translate Δ = Δ' ->
    forall Σ T1 T2,
      okGadt Σ ->
      entails_semantic' Σ Δ' (T1 ≡ T2) <-> entails_semantic Σ Δ (T1 ≡ T2).
  introv Htr. induction T1; destruct T2; introv Hgadt.
  constructor; intro Hsem.
  - unfold entails_semantic' in *; unfold entails_semantic in *;
      unfold alpha_equivalent in *.
    introv HΘ.
  (* introv Htr Hgadt. *)
  (* constructor; introv Hentails; *)
  (*   unfold entails_semantic' in *; unfold entails_semantic in *; *)
  (*     introv Hmatch; *)
  (*     apply Hentails; *)
  (*     lets Heq: subst_equivalence Hgadt Htr; *)
  (*     apply* Heq. *)
Abort.

End TypCtxDefEquivalence.
