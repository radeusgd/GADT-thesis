(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import TLC.LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping.

(** * Sel-<: Premise
    This lemma corresponds to Lemma 3.5 in the paper.

    [inert G]                    #<br>#
    [G ⊢## x: {A: S..U}]        #<br>#
    [――――――――――――――――――――――――――――]   #<br>#
    [exists T. G ⊢## x: {A: T..T}]   #<br>#
    [G ⊢# T <: U]               #<br>#
    [G ⊢# S <: T]                    *)
Lemma sel_premise: forall G x A S U,
  inert G ->
  G ⊢## x : typ_rcd (dec_typ A S U) ->
  exists T V,
    G ⊢! x : V ⪼ typ_rcd (dec_typ A T T) /\
    G ⊢# T <: U /\
    G ⊢# S <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - lets Hp: (pf_dec_typ_inv HG H). subst.
    exists U T. split*.
  - specialize (IHHinv A T U0 HG eq_refl).
    destruct IHHinv as [V [V' [Hx [Hs1 Hs2]]]].
    exists V V'. split*.
Qed.

(** * Sel-<: Replacement
    This lemma corresponds to Lemma 3.4 in the paper.

    [inert G]              #<br>#
    [G ⊢# x: {A: S..U}]   #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢# x.A <: U]       #<br>#
    [G ⊢# S <: x.A]            *)
Lemma sel_replacement: forall G x A S U,
    inert G ->
    G ⊢# trm_var (avar_f x) : typ_rcd (dec_typ A S U) ->
    (G ⊢# typ_sel (avar_f x) A <: U /\
     G ⊢# S <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (tight_to_invertible HG Hty) as Hinv.
  pose proof (sel_premise HG Hinv) as [T [V [Ht [Hs1 Hs2]]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.

Reserved Notation "G '::' T1 '==' T2" (at level 40).

Inductive syntactic_eq_typ : ctx -> typ -> typ -> Prop :=
| seqt_refl : forall G T,
    G :: T == T
| seqt_and_l : forall G T T1 T2,
    G :: T1 == T ->
    G :: T2 == T ->
    G :: (typ_and T1 T2) == T
| seqt_and_r : forall G T T1 T2,
    G :: T1 == T ->
    G :: T2 == T ->
    G :: T == (typ_and T1 T2)
| seqt_and_bot_l1 : forall G T1 T2,
    G :: T1 == typ_bot ->
    G :: (typ_and T1 T2) == typ_bot
| seqt_and_bot_l2 : forall G T1 T2,
    G :: T2 == typ_bot ->
    G :: (typ_and T1 T2) == typ_bot
| seqt_and_bot_r1 : forall G T1 T2,
    G :: T1 == typ_bot ->
    G :: typ_bot == (typ_and T1 T2)
| seqt_and_bot_r2 : forall G T1 T2,
    G :: T2 == typ_bot ->
    G :: typ_bot == (typ_and T1 T2)
| seqt_in_dec_typ : forall G A S1 S2 T1 T2,
    G :: S1 == S2 ->
    G :: T1 == T2 ->
    G :: (typ_rcd (dec_typ A S1 T1)) == (typ_rcd (dec_typ A S2 T2))
| seqt_in_dec_trm : forall G x T1 T2,
    G :: T1 == T2 ->
    G :: (typ_rcd (dec_trm x T1)) == (typ_rcd (dec_trm x T2))

(*
| subtyp_all_t: forall L G S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢# typ_all S1 T1 <: typ_all S2 T2
 *)
| seqt_in_all : forall G S1 S2 T1 T2,
    G :: S1 == S2 ->
    G :: T1 == T2 ->
    G :: (typ_all S1 T1) == (typ_all S2 T2)
| seqt_sel_l : forall G x A U T,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    G :: (typ_sel (avar_f x) A) == T
| seqt_sel_r : forall G x A U T,
    G ⊢! x : U ⪼ typ_rcd (dec_typ A T T) ->
    G :: T == (typ_sel (avar_f x) A)
where "G '::' T1 '==' T2" := (syntactic_eq_typ G T1 T2).

Lemma seqt_sym : forall G T U,
    G :: T == U ->
    G :: U == T.
  introv EQ.
  induction EQ; try solve [try constructor; auto].
  - apply* seqt_sel_r.
  - apply* seqt_sel_l.
Qed.

Lemma seqt_implies_sub : forall G T U,
    G :: T == U ->
    G ⊢# T <: U /\ G ⊢# U <: T.
  induction 1;
    repeat (match goal with
            | H: ?A /\ ?B |- _ => destruct H
           end);
    split~;
         try solve [
           apply subtyp_trans_t with T1; auto
         | apply subtyp_trans_t with T2; auto
         | apply* subtyp_sel1_t
         | apply* subtyp_sel2_t
         ].
  - admit.
  - admit.
Admitted.

(* Lemma subeq_implies_seqt_question_mark : forall G T U, *)
(*     G ⊢# T <: U -> *)
(*     G ⊢# U <: T -> *)
(*               G :: T == U. *)
(*   introv sub1 sub2. *)
(*   dependent induction sub1; *)
(*     repeat (match goal with *)
(*             | H: ?A /\ ?B |- _ => destruct H *)
(*            end). *)
(*     split~; *)
(*          try solve [ *)
(*            apply subtyp_trans_t with T1; auto *)
(*          | apply subtyp_trans_t with T2; auto *)
(*          | apply* subtyp_sel1_t *)
(*          | apply* subtyp_sel2_t *)
(*          ]. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)

Lemma seqt_top_bot : forall G,
    G :: typ_top == typ_bot -> False
with seqt_bot_top : forall G,
    G :: typ_bot == typ_top -> False.
  - intros.
    dependent induction H; auto.
    apply* seqt_bot_top.
  - intros.
    dependent induction H; auto.
    apply* seqt_top_bot.
Qed.

Lemma typ_bot_inv_and : forall G T U,
    G :: typ_and T U == typ_bot ->
    G :: T == typ_bot \/ G :: U == typ_bot.
  introv EQ.
  dependent induction EQ.

Lemma inv_bot : forall G S T,
    inert G ->
    G :: T == typ_bot ->
    G ⊢# S <: T ->
    G :: S == typ_bot.
  introv Hi EQ HS.
  dependent induction HS;
    try solve [constructor | auto].
  - false* seqt_top_bot.
  - apply* seqt_and_bot_l.
  - apply* seqt_and_bot_r.
  - 
  - apply seqt_refl.
  induction 3. ; introv Hi HS.
    try solve [inversion HS].

Lemma invtyping : forall G A S1 S2 T1 T2,
  inert G ->
  G ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2) ->
  G ⊢# T1 <: T2 /\ G ⊢# S2 <: S1.
  introv Hi HS.
  dependent induction HS; auto.
  destruct T.
  - admit.
  - admit.
  - destruct d as [B S0 T0 | a T].
    + specialize (IHHS1 A S1 S0 T1 T0).
      specialize (IHHS2 A S0 S2 T0 T2).
      forwards ~ []: IHHS1.
      * admit.
      * forwards ~ []: IHHS2.
        -- admit.
        -- split*.
    + admit.
  - (* and *) admit.
  - (* sel *) admit.
  - admit.
  - admit.
Admitted.

(** * General to Tight [⊢ to ⊢#] *)
(** The following lemma corresponds to Theorem 3.3 in the paper.
    It says that in an inert environment, general typing ([ty_trm] [⊢]) can
    be reduced to tight typing ([ty_trm_t] [⊢#]).
    The proof is by mutual induction on the typing and subtyping judgements.

    [inert G]           #<br>#
    [G ⊢ t: T]          #<br>#
    [――――――――――――――]    #<br>#
    [G ⊢# t: T] #<br># #<br>#

    and                 #<br># #<br>#
    [inert G]           #<br>#
    [G ⊢ S <: U]        #<br>#
    [――――――――――――――――]  #<br>#
    [G ⊢# S <: U]         *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G t T,
     G ⊢ t : T ->
     G = G0 ->
     G ⊢# t : T) /\
  (forall G S U,
     G ⊢ S <: U ->
     G = G0 ->
     G ⊢# S <: U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply sel_replacement; auto]; eauto.
  - 
Qed.

(** The general-to-tight lemma, formulated for term typing. *)
Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G ⊢ t : T ->
  G ⊢# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
