(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Replacement (Introduction-qp) Typing *)

(** This module contains lemmas related to replacement typing
    ([|-//] and [|-//v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Sequences.
Require Import Definitions Binding InvertibleTyping Narrowing PreciseTyping
        RecordAndInertTypes Replacement Subenvironments TightTyping Weakening.

(** Whereas invertible typing does replacement for singleton types in one direction,
    replacement typing does the replacment in the other direction.

    Note that we can't simply define this using three rules:
    1) identity from invertible typing
    2) two repl subtyping rules
    The reason is that if we did that, repl typing would necessarily apply the replacement
    in all subterms of a term, whereas we want to be able to say, for example:
    [Г ⊢## p: T] #<br>#
    [Г ⊢// p: U] #<br>#
    [__________] #<br>#
    [Г ⊢// p: T ∧ U] #<br>#
 *)

(** ** Replacement Typing for Paths *)

Reserved Notation "G '⊢//' p ':' T" (at level 40, p at level 59).

Inductive ty_repl : ctx -> path -> typ -> Prop :=

(** [G ⊢## p: T]     #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢// p: T]     *)
| ty_inv_r : forall G p T,
    G ⊢## p: T ->
    G ⊢// p: T

(** [G ⊢// p : T]     #<br>#
    [G ⊢// p : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢// p : T /\ U]      *)
| ty_and_r : forall G p T U,
    G ⊢// p: T ->
    G ⊢// p: U ->
    G ⊢// p: T ∧ U

(** [G ⊢## p : T^p]  #<br>#
    [――――――――――――――] #<br>#
    [G ⊢## p : μ(T)]      *)
| ty_bnd_r : forall G p T,
    G ⊢// p: open_typ_p p T ->
    G ⊢// p: μ T

(** [G ⊢// p : T]             #<br>#
    [G ⊢! q: _ ⪼ {A: T..T}]  #<br>#
    [―――――――――――――――――――――――] #<br>#
    [G ⊢//p : q.A]      *)
| ty_sel_r : forall G p T q S A,
    G ⊢// p: T ->
    G ⊢! q: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢// p: q↓A

(** [G ⊢// p.a: T]    #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢// p: {a: T}]     *)
| ty_rcd_intro_r : forall G p a T,
    G ⊢// p•a : T ->
    G ⊢// p : typ_rcd { a ⦂ T }

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: μ(T)]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: μ(T[q/p])]      *)
| ty_rec_qp_r : forall G p q r T T' U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢// r : μ T ->
    repl_typ q p T T' ->
    G ⊢// r : μ T'

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: r'.A]             #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: (r'.A)[q/p]]      *)
| ty_sel_qp_r : forall G p q r r' r'' A U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢// r : r'↓A ->
    repl_typ q p (r'↓A) (r''↓A) ->
    G ⊢// r : r''↓A

(** [G ⊢! p: q.type ⪼ q.type]   #<br>#
    [G ⊢!! q]                   #<br>#
    [G ⊢// r: r'.type]          #<br>#
    [――――――――――――――――――――]      #<br>#
    [G ⊢// p: (r'.type)[q/p]]      *)
| ty_sngl_qp_r : forall G p q r r' r'' U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢// r : {{ r' }} ->
    repl_typ q p {{ r'}} {{ r'' }} ->
    G ⊢// r : {{ r'' }}

where "G '⊢//' p ':' T" := (ty_repl G p T).

Hint Constructors ty_repl.

(** *** From Replacement To Precise Typing *)

(** Replacement-to-precise typing for function types:
    if [G ⊢// p: forall(S)T] then
    - [exists S', T'. G ⊢!!! p: forall(S')T'],
    - [G ⊢# S <: S'], and
    - [G ⊢# T'^y <: T^y],
    where [y] is fresh. *)
Lemma repl_to_precise_typ_all: forall G p S T,
  inert G ->
  G ⊢// p : ∀(S) T ->
  exists S' T' L,
    G ⊢!!! p : ∀(S') T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hp. inversions Hp. apply* invertible_to_precise_typ_all.
Qed.

(** Replacement-to-precise typing for records:
    if [G |-// p: {A: S..U}] then
    - [exists T. G |-// p: {A: T..T}],
    - [G |-# T <: U], and
    - [G |-# S <: T] *)
Lemma repl_to_precise_rcd: forall G p A S U,
  inert G ->
  G ⊢// p : typ_rcd {A >: S <: U} ->
  exists T,
    G ⊢!!! p : typ_rcd {A >: T <: T} /\
    G ⊢# T <: U /\
    G ⊢# S <: T.
Proof.
  introv HG Hr. dependent induction Hr.
  apply* invertible_to_precise_rcd.
Qed.

(** *** Properties of replacement typing *)

Lemma repl_and: forall G p T U,
    inert G ->
    G ⊢// p: T ∧ U ->
    G ⊢// p: T /\ G ⊢// p: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct (invertible_and Hi H). split*.
Qed.

(** Replacement typing is closed under [qp] replacement
    when we know [q]'s precise type *)
Lemma replacement_repl_closure_qp : forall G p q r T T' U,
    inert G ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr Hp.
  gen q r T' U. induction Hp; introv Hq; introv Hr' Hr; try solve [invert_repl; eauto 5].
  - Case "ty_inv_r"%string.
    gen q r T' U. induction H; introv Hq; introv Hr; introv Hr'; try solve [invert_repl; eauto 5].
    -- SCase "ty_precise_inv"%string.
       destruct (pt3_inertsngl Hi H) as [[Hit | Hs] | Hst].
       + SSCase "ty_precise_inv_1"%string.
         inversions Hit; invert_repl.
         ++ apply ty_inv_r. eapply ty_all_inv with (L := \{}).
            apply* ty_precise_inv. apply repl_swap in H5.
            eauto. introv Hy. auto.
         ++ apply ty_inv_r.
            eapply ty_all_inv with (L := dom G).
            apply* ty_precise_inv. auto. introv Hy.
            eapply repl_open_var in H5; try solve_names.
            eapply subtyp_sngl_qp. apply* weaken_ty_trm.
            eapply precise_to_general. apply Hq. apply* weaken_ty_trm. apply* precise_to_general2. apply H5.
         ++ apply* ty_rec_qp_r.
       + SSCase "ty_precise_inv_2"%string.
         inversions Hs. invert_repl. eauto.
       + SSCase "ty_precise_inv_3"%string.
         inversion Hst as [x Hx].
         generalize dependent T'.
         dependent induction Hx; introv Hr; subst; invert_repl.
         ++ apply ty_inv_r. destruct D2.
            * invert_repl; apply ty_precise_inv in H;
              eapply ty_dec_typ_inv; eauto.
              assert (Hts : G ⊢# t0 <: T1).
              { apply repl_swap in H6. eauto. }
              eauto.
            * invert_repl. eapply ty_precise_inv in H.
              eapply ty_dec_trm_inv; eauto.
        ++ assert (Hpt0 : G ⊢!!! p : T) by (eapply pt3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pt3_and_destruct2; eauto).
           apply* ty_and_r.
        ++ assert (Hpt0 : G ⊢!!! p : T) by (eapply pt3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pt3_and_destruct2; eauto).
          apply ty_and_r; eauto. apply ty_inv_r.
          destruct D2; invert_repl;
          apply ty_precise_inv in Hpd.
          * eapply ty_dec_typ_inv; eauto.
            apply repl_swap in H7. eauto.
          * eapply ty_dec_typ_inv; eauto.
          * eapply ty_dec_trm_inv; eauto.
    -- SCase "ty_dec_trm_inv"%string.
       invert_repl. eapply ty_inv_r. eapply ty_dec_trm_inv.
       apply H. apply subtyp_trans_t with (T:=U); eauto.
    -- SCase "ty_dec_typ_inv"%string.
       invert_repl.
         * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
           eapply subtyp_trans_t. apply repl_swap in H9.
           eapply subtyp_sngl_pq_t. eauto. eauto.
           apply H9. auto. auto.
         * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
           eauto. eapply subtyp_trans_t. apply H1. eauto.
    -- SCase "ty_all_inv"%string.
       invert_repl; apply ty_inv_r.
       + eapply ty_all_inv with (L := L \u (dom G)).
         * apply H.
         * assert (Hts : G ⊢# T3 <: S2).
           { apply repl_swap in H7. eauto. }
           eauto.
         * introv Hy. eapply narrow_subtyping.
           apply H1. eauto.
           assert (Hts : G ⊢ T3 <: S2).
           { apply tight_to_general.
           apply repl_swap in H7. eauto. }
           constructor; eauto.
       + eapply ty_all_inv with (L := L \u (dom G)).
         * eauto.
         * assumption.
         * introv Hy. eapply subtyp_trans.
           apply* H1. eapply repl_open_var in H7.
           ** eapply subtyp_sngl_qp.
              apply precise_to_general in Hq.
              apply weaken_ty_trm. apply Hq. eauto.
              apply weaken_ty_trm. apply* precise_to_general2. eauto.
              eauto.
           ** solve_names.
           ** apply precise_to_general_h in Hq as [Hq].
              eapply typed_paths_named. apply Hq.
    -- SCase "ty_sel_qp_inv"%string.
       inversions Hr. eauto.
    -- SCase "ty_sngl_qp_inv"%string.
       inversions Hr. eauto.
  - Case "ty_sel_qp_r"%string.
    lets ?: (ty_sel_qp_r H H0 Hp H1). invert_repl. eauto.
  - Case "ty_sngl_qp_r"%string.
    lets ?: (ty_sngl_qp_r H H0 Hp H1). invert_repl. eauto.
Qed.

(** Replacement typing is closed under [qp] replacement
    when we know [q]'s II-level precise type *)
Lemma replacement_repl_closure_qp2 : forall G p q r T T' U,
    inert G ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr' Hp Hr. gen U. dependent induction Hq; introv Hr'.
  - lets Heq: (pf_sngl_T Hi H). subst.
    apply* replacement_repl_closure_qp.
  - pose proof (repl_field_elim _ _ _ Hr) as Hr''.
    pose proof (pt2_backtrack _ _ Hr') as [U' Hq]. eauto.
Qed.

(** Replacement typing is closed under [qp] replacement
    when we know [q]'s III-level precise type *)
Lemma replacement_repl_closure_qp3 : forall G p q r T T' U,
    inert G ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢// p : T ->
    repl_typ r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hr' Hp Hr. gen p T T' U. dependent induction Hq; introv Hp; introv Hr; introv Hr'.
  - apply* replacement_repl_closure_qp2.
  - specialize (IHHq _ Hi eq_refl _ _ Hp).
    destruct (repl_insert q Hr) as [V [Hr1 Hr2]].
    pose proof (pt2_exists Hq) as [S Hs].
    specialize (IHHq _ Hr1 _ Hr'). eapply replacement_repl_closure_qp2.
    auto. apply H. apply Hs. apply IHHq. eauto.
Qed.

(** Replacement typing is closed under repeated [qp] replacements *)
Lemma replacement_repl_closure_qp_comp: forall G p q r T T' U,
    inert G ->
    G ⊢// p: T ->
    G ⊢!!! q: {{ r }} ->
    G ⊢!! r : U ->
    repl_repeat_typ r q T T' ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hq Hr Hc. gen p. dependent induction Hc; introv Hp; eauto.
  apply* IHHc. apply* replacement_repl_closure_qp3.
Qed.

(** Replacement typing is closed under opening of recursive types *)
Lemma repl_rec_intro: forall G p T,
    inert G ->
    G ⊢// p: μ T ->
    G ⊢// p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - Case "ty_inv_r"%string.
    destruct* (invertible_bnd Hi H) as [Hr | [q [U [Hr [[S Hs]%pt2_exists Hr']]]]].
    eapply replacement_repl_closure_qp_comp. auto. apply* ty_inv_r.
    apply Hr. eauto.
    apply* repl_comp_open.
  - Case "ty_rec_pq_r"%string.
    specialize (IHHp _ Hi eq_refl).
    apply repl_open with (r:= r) in H1; try solve_names. apply* replacement_repl_closure_qp.
Qed.

Lemma replacement_repl_closure_pq_helper_mutind: (forall q p T T',
    repl_typ q p T T' ->
    forall q0 r0 T2 G, repl_typ q0 r0 T' T2 ->
    inert G ->
    G ⊢! p: {{ q }} ⪼ {{ q }} ->
    G ⊢! q0: {{ r0 }} ⪼ {{ r0 }} ->
             T = T2 \/ exists T3, repl_typ q0 r0 T T3 /\ repl_typ q p T3 T2) /\
    (forall q p D D',
        repl_dec q p D D' ->
    forall q0 r0 D2 G,
    repl_dec q0 r0 D' D2 ->
    inert G ->
    G ⊢! p: {{ q }} ⪼ {{ q }} ->
    G ⊢! q0: {{ r0 }} ⪼ {{ r0 }} ->
    D = D2 \/ exists D3, repl_dec q0 r0 D D3 /\ repl_dec q p D3 D2).
Proof.
  apply repl_mutind; intros; eauto.
  - invert_repl. destruct (H _ _ _ _ H7 H1 H2 H3); subst; eauto.
    right. destruct H0 as [D4 [Hl Hr]]. exists (typ_rcd D4). split; eauto.
  - invert_repl.
    * destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T5 [Hl Hr]]. exists (T5 ∧ U). split; eauto.
    * right. exists (T1 ∧ T4). split; auto.
  - inversions H0.
    * right. exists (T4 ∧ T1). split; auto.
    * destruct (H _ _ _ _ H9 H1 H2 H3). rewrite H0. auto.
      destruct H0 as [T5 [Hl Hr]]. right. exists (U ∧ T5). split; auto.
  - inversions H. left. assert (p •• bs = r0 •• bs0).
    eapply pf_sngl_sel_unique; eauto. rewrite H. auto.
  - inversions H0. destruct (H _ _ _ _ H7 H1 H2 H3); subst; eauto.
    right. destruct H0 as [T5 [Hl Hr]]. exists (μ T5). split; auto.
  - invert_repl.
    * destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T5 [Hl Hr]]. exists (∀ (T5) U). split; auto.
    * right. exists (∀ (T1) T4). split; auto.
  - invert_repl.
    * right. exists (∀ (T4) T1). split; auto.
    * destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T5 [Hl Hr]]. exists (∀ (U) T5). split; auto.
  - invert_repl. left. assert (p •• bs = r0 •• bs0).
    eapply pf_sngl_sel_unique; eauto. rewrite H. auto.
  - invert_repl.
    * destruct (H _ _ _ _ H10 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T4 [Hl Hr]]. exists (dec_typ A T4 U). split; auto.
    * right. exists (dec_typ A T1 T3). split; auto.
  - invert_repl.
    * right. exists (dec_typ A T3 T1). split; auto.
    * destruct (H _ _ _ _ H10 H1 H2 H3); subst; eauto.
      right. destruct H0 as [T4 [Hl Hr]]. exists (dec_typ A U T4). split; auto.
  - invert_repl. destruct (H _ _ _ _ H9 H1 H2 H3); subst; eauto.
    right. destruct H0 as [T4 [Hl Hr]]. exists ({a ⦂ T4}). split; auto.
Qed.

Lemma replacement_repl_closure_pq_helper: forall p q T T',
    repl_typ q p T T' ->
    forall q0 r0 T2 G, repl_typ q0 r0 T' T2 ->
    inert G ->
    G ⊢! p: {{ q }} ⪼ {{ q }} ->
    G ⊢! q0: {{ r0 }} ⪼ {{ r0 }} ->
    T = T2 \/ exists T3, repl_typ q0 r0 T T3 /\ repl_typ q p T3 T2.
Proof.
  destruct replacement_repl_closure_pq_helper_mutind; eauto.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s precise type *)
Lemma replacement_repl_closure_pq : forall G p q r T T' U,
    inert G ->
    G ⊢// p : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hqr.
  gen q r T' U. induction Hp; introv Hq; introv Hr' Hr; eauto.
   - Case "ty_inv_r"%string.
     constructor. apply* invertible_repl_closure.
   - Case "ty_and_r"%string.
     invert_repl; eauto.
   - Case "ty_bnd_r"%string.
     invert_repl. apply (repl_open p) in H2; try solve_names. eauto.
   - Case "ty_sel_r"%string.
     clear IHHp. invert_repl. lets Heq: (pf_sngl_flds_elim _ Hi Hq H). subst.
     rewrite field_sel_nil in *.
     lets Heq: (pf_T_unique Hi H Hq). subst.
     apply pf_sngl_U in H. inversion H.
   - Case "ty_rcd_intro_r"%string. invert_repl. eauto.
   - Case "ty_rec_qp_r"%string.
     invert_repl. specialize (IHHp Hi _ _ Hq).
     destruct (replacement_repl_closure_pq_helper H1 H5 Hi H Hq).
     * rewrite <- H2. auto.
     * destruct H2 as [T3 [Hl Hr]].
       assert (G ⊢// r : μ T3) by (eapply IHHp; eauto).
       apply (ty_rec_qp_r H H0 H2 Hr).
   - Case "ty_sel_pq_r"%string. invert_repl.
     assert (q •• bs0 = r0 •• bs).
     eapply pf_sngl_sel_unique; eauto. rewrite <- H1. auto.
   - Case "ty_sngl_pq_r"%string. invert_repl.
     assert (q •• bs0 = r0 •• bs).
     eapply pf_sngl_sel_unique; eauto. rewrite <- H1. auto.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s II-level precise type *)
Lemma replacement_repl_closure_pq2 : forall G p q r T T' U,
    inert G ->
    G ⊢// p : T ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hr' Hr. gen U. dependent induction Hq; introv Hr'.
  - apply* replacement_repl_closure_pq. lets Heq: (pf_sngl_T Hi H). subst. auto.
  - pose proof (repl_field_elim _ _ _ Hr).
    pose proof (pt2_backtrack _ _ Hr') as [U' Hq'].
    specialize (IHHq1 _ Hi Hp eq_refl H _ Hq').
    eauto.
Qed.

(** Replacement typing is closed under [pq] replacement
    when we know [q]'s III-level precise type *)
Lemma replacement_repl_closure_pq3 : forall G p q r T T' U,
    inert G ->
    G ⊢// p : T ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hr. gen p T U. dependent induction Hq; introv Hp; introv Hr' Hr.
  - apply* replacement_repl_closure_pq2.
  - destruct (repl_insert q Hr) as [U' [Hr1 Hr2]].
    pose proof (pt2_exists Hq) as [S Hq'].
    lets Hc: (replacement_repl_closure_pq2 Hi Hp H Hq' Hr1). apply* IHHq.
Qed.

(** Replacement typing is closed under repeated [pq] replacement *)
Lemma replacement_repl_closure_pq_comp: forall G p q r T T' U,
    inert G ->
    G ⊢// p: T ->
    G ⊢!!! q: {{ r }} ->
    G ⊢!! r : U ->
    repl_repeat_typ q r T T' ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hq Hr Hc. gen p. dependent induction Hc; introv Hp; eauto.
  apply* IHHc. apply* replacement_repl_closure_pq3.
Qed.

(** Replacement typing is closed under [<:-Sel] subtyping when
    we know that a path's II-level precise type has a type member *)
Lemma path_sel_repl2: forall G p A T q,
    inert G ->
    G ⊢!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : T ->
    G ⊢// q : p ↓ A.
Proof.
  introv Hi Hp Hq. dependent induction Hp; eauto.
Qed.

(** Replacement typing is closed under [<:-Sel] subtyping when
    we know that a path's III-level precise type has a type member *)
Lemma path_sel_repl: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : T ->
    G ⊢// q : p ↓ A.
Proof.
  introv Hi Hp Hq. dependent induction Hp; eauto.
  apply* path_sel_repl2.
  specialize (IHHp _ _ Hi eq_refl Hq).
  assert (forall q, q = q •• nil) as Hnil. {
    intro. rewrite* field_sel_nil.
  }
  lets He1: (Hnil q0). lets He2: (Hnil p).
  pose proof (pt2_exists Hp) as [U Hp0].
  eapply (replacement_repl_closure_qp2 Hi H Hp0 IHHp).
  rewrite He1 at 2. rewrite He2 at 2. apply rpath.
Qed.

(** Replacement typing is closed under [Sel-<:] subtyping *)
Lemma path_sel_repl_inv: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : p ↓ A ->
    G ⊢// q : T.
Proof.
  introv Hi Hp Hq. dependent induction Hq.
  - Case "ty_inv_r"%string.
    constructor. apply* path_sel_inv.
  - Case "ty_sel_r"%string.
    clear IHHq. lets Heq: (pf_pt3_unique Hi H Hp). subst*.
  - Case "ty_sel_qp_r"%string.
    destruct (repl_prefixes_sel H1) as [bs [He1 He2]].
    subst. assert (record_type (typ_rcd {A >: T <: T})) as Hrt by eauto.
    lets Hqbs: (pf_pt3_trans_inv_mult' _ Hi H Hp (or_intror Hrt)). apply* IHHq.
Qed.

(** If a path has a replacement type it has also an invertible type *)
Lemma repl_to_inv G p T :
  G ⊢// p : T ->
  exists U, G ⊢## p : U.
Proof.
  induction 1; eauto. destruct IHty_repl as [U Hp].
  clear H. apply inv_backtrack in Hp. eauto.
Qed.

(** Replacement typing is closed under ⊤-subtyping *)
Lemma repl_top: forall G r T,
    G ⊢// r: T ->
    G ⊢// r: ⊤.
Proof.
  introv Hr. apply repl_to_inv in Hr as [? ?]. constructor*.
Qed.
