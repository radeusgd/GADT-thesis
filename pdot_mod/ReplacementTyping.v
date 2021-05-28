(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Replacement (Introduction-qp) Typing Part 2 *)

(** This module contains lemmas related to replacement typing
    ([|-//] and [|-//v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List String.
Require Import Sequences.
Require Import Definitions Binding InvertibleTyping Narrowing PreciseTyping
        RecordAndInertTypes Replacement Subenvironments TightTyping Weakening.

Require Export ReplacementTyping1.

(** Replacement typing is closed under tight subtyping *)
Lemma replacement_subtyping_closure : forall G T U p,
    inert G ->
    G ⊢# T <: U ->
    G ⊢// p: T ->
    G ⊢// p: U.
Proof.
  introv Hi Hs. gen p. induction Hs; introv Hp; auto.
  - Case "subtyp_top"%string.
    apply* repl_top.
  - Case  "subtyp_bot"%string.
    inversions Hp. false* invertible_bot.
  - Case "subtyp_and1"%string.
    apply (repl_and Hi) in Hp. destruct_all. auto.
  - Case "subtyp_and2"%string.
    apply (repl_and Hi) in Hp. destruct_all. auto.
  - Case "subtyp_fld"%string.
    dependent induction Hp; eauto.
  - Case "subtyp_typ"%string.
    dependent induction Hp; eauto.
(*   - Case "subtyp_typ_inv1"%string. *)
(*     (* Check ty_dec_typ_inv. *) *)
(*     (* eapply ty_dec_typ_inv. *) *)
(*     (* apply ty_precise_inv. *) *)
(*     (* Check pt3. *) *)
(*     admit. *)
(*     (* *)
(* Debug: 1 depth=5 *)
(* Debug: 1.1 depth=4 simple apply ty_inv_r *)
(* Debug: 1.1.2 depth=3 simple eapply ty_dec_typ_inv *)
(* Debug: 1.1.2.1 depth=3 exact H *)
(* Debug: 1.1.2.1.1 depth=3 exact Hs1 *)
(* Debug: 1.1.2.1.1.1 depth=3 exact Hs2 *)
(*      *) *)
(*   - Case "subtyp_typ_inv2"%string. *)
(*     admit. *)
  - Case "subtyp_sngl_pq"%string.
    pose proof (pt2_exists H0) as [? ?].
    apply* replacement_repl_closure_pq3.
  - Case "subtyp_sngl_qp"%string.
    pose proof (pt2_exists H0) as [? ?].
    apply* replacement_repl_closure_qp3.
  - Case "subtyp_sel2"%string.
    apply* path_sel_repl.
  - Case "subtyp_sel1"%string.
    apply* path_sel_repl_inv.
  - Case "subtyp_all"%string.
    dependent induction Hp; eauto.
Qed.

(** If a path has a replacement type it also has a III-level precise type *)
Lemma repl_prec_exists: forall G p T,
    G ⊢// p: T ->
    exists U, G ⊢!!! p: U.
Proof.
  introv Hp. apply repl_to_inv in Hp as [? Hp].
  induction Hp; eauto.
Qed.

(** Replacement is closed under field selection on paths *)
Lemma repl_fld : forall G p a T,
    inert G ->
    G ⊢// p: typ_rcd {a ⦂ T} ->
    G ⊢// p•a : T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  dependent induction H; eauto.
  - dependent induction H.
    * dependent induction H; eauto.
      apply pf_fld in H; apply ty_inv_r; apply* ty_precise_inv.
    * lets Hq: (pt3_field_elim H0).
      lets Hp: (pt3_trans _ H Hq). eauto.
  - specialize (IHty_path_inv _ _ eq_refl Hi). apply ty_inv_r in H.
    eapply replacement_subtyping_closure. auto. apply H0. auto.
Qed.

(** If [G ⊢// p: T] and [T] and [T'] are equivalent then [G ⊢// p: T'] *)
Lemma replacement_repl_closure_comp_typed: forall G p T T',
    inert G ->
    G ⊢// p: T ->
    G ⊢ T' ⟿ T ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  destruct H as [p' [q' [S [Hpq [Hq Hr']]]]].
  lets Hrc: (replacement_repl_closure_qp Hi Hpq Hq Hp Hr'). eauto.
Qed.

(** From replacement typing of singleton types to invertible typing of singleton types *)
Lemma repl_to_invertible_sngl_repl_comp: forall G p q,
    inert G ->
    G ⊢// p: {{ q }} ->
    exists q', G ⊢ q ⟿' q' /\ G ⊢## p: {{ q' }}.
Proof.
  introv Hi Hp. dependent induction Hp.
  - Case "ty_inv_r"%string.
    exists q. split*. apply star_refl.
  - Case "ty_sngl_qp_r"%string.
    specialize (IHHp _ Hi eq_refl). destruct IHHp as [p' [Hr Hr']].
    eexists. split*. eapply star_trans. apply Hr.  apply star_one. repeat eexists; eauto.
Qed.

(** If a path [p] has type [q.type] under replacement typing and [q] is well-typed,
    then the invertible type of [p] has a singleton type [q'.type], and [q] and [q']
    are aliases. *)
Lemma repl_to_invertible_sngl: forall G p q U,
    inert G ->
    G ⊢// p: {{ q }} ->
    G ⊢!! q : U ->
    exists q' S, G ⊢## p: {{ q' }} /\ G ⊢!! q' : S /\ (q = q' \/ G ⊢!!! q: {{ q' }}).
Proof.
  introv Hi Hp Hq. gen U. dependent induction Hp; introv Hq.
  - repeat eexists; eauto.
  - invert_repl.
    pose proof (pf_pt2_trans_inv_mult _ Hi H Hq) as ->.
    pose proof (pt2_qbs_typed _ Hi H H0 Hq) as [S Hq'].
    specialize (IHHp _ Hi eq_refl _ Hq') as [q' [W [Hrq' [Hq'' [<- | Hqq']]]]]; repeat eexists; eauto.
Qed.

(** If [p]'s replacement type is [q.type] and [q] is well-typed, then
    [p.a]'s replacement type is [q.a.type] *)
Lemma path_elim_repl: forall G p q a T,
    inert G ->
    G ⊢// p: {{ q }} ->
    G ⊢// q•a : T ->
    G ⊢// p•a : {{ q•a }}.
Proof.
  introv Hi Hp Hq.
  destruct (repl_to_invertible_sngl_repl_comp Hi Hp) as [p' [Hc Hpi]].
  destruct (repl_comp_sngl_inv1 Hc) as [r Heq]. inversions Heq.
  destruct (inv_to_precise_sngl_repl_comp Hpi) as [r' [Hp' Hrc]].
  destruct (repl_prec_exists Hq) as [U Hq']. clear Hq.
  destruct (field_typing_comp1 _ Hi Hc Hq') as [T1 Hra].
  destruct (field_typing_comp2 _ Hi Hrc Hra) as[T2 Hr'a].
  lets Hper: (path_elim_prec _ Hi Hp' Hr'a).
  lets Hinv: (ty_precise_inv Hper).
  assert (G ⊢ r' • a ⟿' r • a) as Hr'
    by apply* repl_composition_fld_elim.
  assert (G ⊢ q • a ⟿' r • a) as Hr''
   by apply* repl_composition_fld_elim.
  lets Hic: (invertible_repl_closure_comp_typed Hi Hinv Hr').
  apply* replacement_repl_closure_comp_typed.
Qed.

(** Replacement typing is closed under singleton transitivity with a type [q.type]
    if [q] is typeable under invertible typing *)
Lemma inv_sngl_trans: forall G p q T,
    inert G ->
    G ⊢// p : {{ q }} ->
    G ⊢## q : T ->
    G ⊢// p : T.
Proof.
  introv Hi Hpq Hq. gen p. induction Hq; introv Hpq; eauto; try solve [apply* replacement_repl_closure_pq].
  - pose proof (pt2_exists H) as [U H'].
    destruct (repl_to_invertible_sngl Hi Hpq H') as [r [S [Hpr [Hq Hrc]]]].
    destruct (inv_to_precise_sngl Hi Hpr (pt3 Hq)) as [r' [Hpr' Hrc']]. clear Hpr Hpq H'.
    destruct Hrc, Hrc'; subst.
    * do 2 constructor. apply* pt3_sngl_trans3.
    * do 2 constructor. repeat apply* pt3_sngl_trans3.
    * lets Hpi: (pt3_invert Hi H H0). destruct_all; subst; auto.
      ** do 2 constructor. apply* pt3_sngl_trans3.
      ** apply ty_precise_inv in Hpr'. apply ty_inv_r in Hpr'.
         apply* replacement_repl_closure_qp3. apply* repl_intro_sngl.
    * lets Hpi: (pt3_invert Hi H H0). destruct_all; subst.
      ** do 2 constructor. do 2 apply* pt3_sngl_trans3.
      ** do 2 constructor. apply* pt3_sngl_trans3.
      ** apply ty_precise_inv in Hpr'. apply ty_inv_r in Hpr'.
         lets Hc: (replacement_repl_closure_pq3 Hi Hpr' H1 Hq (repl_intro_sngl r' r)).
         apply* replacement_repl_closure_qp3. apply* repl_intro_sngl.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_fld_t.
    apply H. auto.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_typ_t.
    apply H. apply H0. auto.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_all_t.
    apply H. apply H0. auto.
  - apply* repl_top.
Qed.

(** Replacement typing is closed under singleton transitivity *)
Lemma repl_sngl_trans: forall G p q T,
    inert G ->
    G ⊢// p : {{ q }} ->
    G ⊢// q : T ->
    G ⊢// p : T.
Proof.
  introv Hi Hpq Hq. gen p. induction Hq; introv Hpq; eauto.
  - apply* inv_sngl_trans.
  - specialize (IHHq Hi _ Hpq). apply ty_bnd_r.
    pose proof (repl_to_inv Hq) as [_ [_ [U Hq']%pt2_exists]%inv_to_prec].
    destruct (repl_to_invertible_sngl Hi Hpq Hq') as [r [S [Hpr [Hs Hor]]]].
    destruct (inv_to_precise_sngl Hi Hpr (pt3 Hs)) as [r' [Hpr' Hor']]. clear Hpr Hpq.
    destruct Hor, Hor'; subst.
    * assert (repl_repeat_typ r p0 (open_typ_p r T) (open_typ_p p0 T)) as Hrr by apply* repl_comp_open_rec.
      apply* replacement_repl_closure_qp_comp.
    * assert (repl_repeat_typ r r' (open_typ_p r T) (open_typ_p r' T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_qp_comp Hi IHHq H0 Hs Hrr).
      apply pt2_exists in H0 as [? ?].
      eapply (replacement_repl_closure_qp_comp Hi Hc). apply Hpr'. eauto.
      apply* repl_comp_open_rec.
    * assert (repl_repeat_typ p r (open_typ_p p T) (open_typ_p r T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_pq_comp Hi IHHq H Hs Hrr).
      apply* replacement_repl_closure_qp_comp. apply* repl_comp_open_rec.
    * assert (repl_repeat_typ p r (open_typ_p p T) (open_typ_p r T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_pq_comp Hi IHHq H Hs Hrr).
      assert (repl_repeat_typ r r' (open_typ_p r T) (open_typ_p r' T)) as Hrr' by apply* repl_comp_open_rec.
      lets Hc': (replacement_repl_closure_qp_comp Hi Hc H0 Hs Hrr').
      pose proof (pt2_exists H0) as [? ?].
      eapply (replacement_repl_closure_qp_comp Hi). auto. apply Hc'. apply Hpr'. eauto. apply* repl_comp_open_rec.
  - pose proof (path_elim_repl _ Hi Hpq Hq) as Hp0a. specialize (IHHq Hi _ Hp0a). eauto.
Qed.

(** Tight typing implies replacement typing *)
Lemma replacement_closure : forall G p T,
  inert G ->
  G ⊢# trm_path p : T ->
  G ⊢// p: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  - Case "ty_var_t"%string.
    repeat econstructor; eauto.
  - Case "ty_new_elim_t"%string.
    apply* repl_fld.
  - Case "ty_sngl_t"%string.
    apply* repl_sngl_trans.
  - Case "ty_path_elim_t"%string.
    apply* path_elim_repl.
  - Case "ty_rec_elim_t"%string.
    specialize (IHHp _ Hi eq_refl). apply* repl_rec_intro.
  - Case "ty_sub_t"%string.
    specialize (IHHp _ Hi eq_refl).
    eapply replacement_subtyping_closure. auto. apply H. auto.
Qed.

(** ** Replacement typing for values

    The definition of replacement typing for values
    is similar to replacement typing for paths, but simpler. The same holds for
    its lemmas. To see the documentation for a replacement-typing-for-values lemma,
    please refer to its replacement-typing-for-paths version. *)

Reserved Notation "G '⊢//v' v ':' T" (at level 40, v at level 59).

Inductive ty_replv : ctx -> val -> typ -> Prop :=
| ty_inv_rv : forall G v T,
    G ⊢##v v: T ->
    G ⊢//v v: T
| ty_and_rv : forall G v T U,
    G ⊢//v v: T ->
    G ⊢//v v: U ->
    G ⊢//v v: T ∧ U
| ty_sel_rv : forall G v T q S A,
    G ⊢//v v: T ->
    G ⊢! q: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢//v v: q ↓ A
| ty_rec_qp_rv : forall G p q v T T' U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : μ T ->
    repl_typ q p T T' ->
    G ⊢//v v : μ T'
| ty_sel_qp_rv : forall G p q v r' r'' A U,
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : r' ↓ A ->
    repl_typ q p (r' ↓ A) (r'' ↓ A) ->
    G ⊢//v v : r''↓A
where "G '⊢//v' v ':' T" := (ty_replv G v T).

Hint Constructors ty_replv.

Lemma invertible_andv: forall G v T U,
    inert G ->
    G ⊢##v v: T ∧ U ->
    G ⊢##v v: T /\ G ⊢##v v: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. inversion H.
Qed.

Lemma repl_andv: forall G v T U,
    inert G ->
    G ⊢//v v: T ∧ U ->
    G ⊢//v v: T /\ G ⊢//v v: U.
Proof.
  introv Hi Hv. dependent induction Hv; eauto.
  destruct (invertible_andv Hi H). split*.
Qed.

Lemma replacement_repl_closure_qp_v G v p q T T' U :
    inert G ->
    G ⊢! p : {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    G ⊢//v v : T ->
    repl_typ q p T T' ->
    G ⊢//v v : T'.
Proof.
  intros Hi Hpq Hq Hv.
  gen p q T' U. induction Hv; introv Hpq; introv Hq Hr.
  - Case "ty_inv_rv"%string.
    gen p q T' U. induction H; introv Hpq; introv Hr; introv Hq;
    try solve [invert_repl; eauto].
    -- destruct (pfv_inert H).
      + invert_repl.
        ++ eapply ty_inv_rv.
           eapply ty_all_invv with (L := \{}).
           eapply ty_precise_invv. apply H.
           apply repl_swap in H5.
           eauto.
           introv Hy. auto.
        ++ eapply ty_inv_rv.
           eapply ty_all_invv with (L := dom G).
           eapply ty_precise_invv. apply H.
           auto.
           introv Hy.
           eapply repl_open_var in H5; try solve_names.
           eapply subtyp_sngl_qp. apply* weaken_ty_trm.
           eapply precise_to_general. apply Hpq. apply weaken_ty_trm; auto. apply* precise_to_general2. apply H5.
      + invert_repl; eauto.
    -- invert_repl; apply ty_inv_rv.
       + eapply ty_all_invv with (L := L \u (dom G)).
         * apply H.
         * assert (Hts : G ⊢# T3 <: S2).
           { apply repl_swap in H7. eauto. }
           eauto.
         * introv Hy. eapply narrow_subtyping.
           apply H1. eauto.
           assert (Hts : G ⊢ T3 <: S2).
           { apply tight_to_general.
           apply repl_swap in H7. eauto. }
           constructor; eauto. (* narrowing *)
       + eapply ty_all_invv with (L := L \u (dom G)).
         * eauto.
         * assumption.
         * introv Hy. eapply subtyp_trans.
           apply* H1. eapply repl_open_var in H7.
           ** eapply subtyp_sngl_qp.
              apply precise_to_general in Hpq.
              apply weaken_ty_trm. apply Hpq. eauto.
              apply weaken_ty_trm; auto. apply* precise_to_general2. eauto.
           ** solve_names.
           ** solve_names.
  - Case "ty_and_rv"%string.
    invert_repl; eauto.
  - Case "ty_sel_rv"%string.
    invert_repl; eauto.
  - Case "ty_rec_qp_rv"%string.
    invert_repl; eauto.
  - Case "ty_sel_qp_rv"%string.
    lets ?: (ty_sel_qp_rv H H0 Hv H1).
    invert_repl; eauto.
Qed.

Lemma replacement_repl_closure_qp2_v : forall G p v r T T' U,
    inert G ->
    G ⊢!! p : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢//v v : T ->
    repl_typ r p T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hp Hr Hv Hrp. gen U. dependent induction Hp; introv Hr.
  - lets Heq: (pf_sngl_T Hi H). subst.
    apply* replacement_repl_closure_qp_v.
  - lets Hr': (repl_field_elim _ _ _ Hrp). pose proof (pt2_backtrack _ _ Hr) as [? Hq']. eauto.
Qed.

Lemma replacement_repl_closure_qp3_v : forall G v p r T T' U,
    inert G ->
    G ⊢!!! p : {{ r }} ->
    G ⊢!! r : U ->
    G ⊢//v v : T ->
    repl_typ r p T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hp Hr Hv Hrp. gen v T T' U. dependent induction Hp; introv Hv; introv Hrp; introv Hr.
  - apply* replacement_repl_closure_qp2_v.
  - specialize (IHHp _ Hi eq_refl).
    destruct (repl_insert q Hrp) as [U' [Hr1 Hr2]].
    pose proof (pt2_exists Hp) as [W Hp'].
    specialize (IHHp _ _ Hv _ Hr1). eapply replacement_repl_closure_qp2_v.
    auto. eauto. eauto. apply* IHHp. eauto.
Qed.

Lemma replacement_repl_closure_pq_v : forall G v q r T T' U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢! q : {{ r }} ⪼ {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hqr Hr'.
  gen q r T' U. induction Hv; introv Hq; introv Hr' Hr; eauto.
   - Case "ty_inv_r"%string.
     constructor. apply* invertible_repl_closure_v.
   - Case "ty_and_r"%string.
     invert_repl; eauto.
   - Case "ty_sel_r"%string.
     clear IHHv. invert_repl. lets Heq: (pf_sngl_flds_elim _ Hi Hq H). subst.
     rewrite field_sel_nil in *.
     lets Heq: (pf_T_unique Hi H Hq). subst.
     apply pf_sngl_U in H. inversion H.
  - Case "ty_rec_qp_r"%string.
    invert_repl. specialize (IHHv Hi _ _ Hq).
    destruct (replacement_repl_closure_pq_helper H1 H5 Hi H Hq).
    * rewrite <- H2. auto.
    * destruct H2 as [T3 [Hl Hr]].
      assert (G ⊢//v v : μ T3) by (eapply IHHv; eauto).
      apply (ty_rec_qp_rv H H0 H2 Hr).
  - Case "ty_sel_pq_r"%string. invert_repl.
    specialize (IHHv Hi _ _ Hq).
    assert (q •• bs0 = r •• bs). eapply pf_sngl_sel_unique; eauto.
    rewrite <- H1. auto.
Qed.

Lemma replacement_repl_closure_pq2_v : forall G v q r T T' U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hq Hr' Hr. gen U. dependent induction Hq; introv Hr'.
  - apply* replacement_repl_closure_pq_v.
    lets Heq: (pf_sngl_T Hi H). subst. auto.
  - lets Hr'': (repl_field_elim _ _ _ Hr). pose proof (pt2_backtrack _ _ Hr') as [? ?]. eauto.
Qed.

Lemma replacement_repl_closure_pq3_v : forall G v q r T T' U,
    inert G ->
    G ⊢//v v : T ->
    G ⊢!!! q : {{ r }} ->
    G ⊢!! r : U ->
    repl_typ q r T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hv Hq Hr Hr'. gen v T U. dependent induction Hq; introv Hv Hr; introv Hr'.
  - apply* replacement_repl_closure_pq2_v.
  - destruct (repl_insert q Hr) as [? [Hr1 Hr2]].
    pose proof (pt2_exists Hq) as [? Hq'].
    lets Hc: (replacement_repl_closure_pq2_v Hi Hv H Hq' Hr1). apply* IHHq.
Qed.

Lemma path_sel_repl2_v: forall G p A T v,
    inert G ->
    G ⊢!! p : typ_rcd {A >: T <: T} ->
    G ⊢//v v : T ->
    G ⊢//v v : p↓A.
Proof.
  introv Hi Hp Hv. dependent induction Hp; eauto.
Qed.

Lemma path_sel_repl_v: forall G p A T v,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢//v v : T ->
    G ⊢//v v : p↓A.
Proof.
  introv Hi Hp Hv. dependent induction Hp; eauto.
  apply* path_sel_repl2_v.
  specialize (IHHp _ _ Hi eq_refl Hv).
  assert (forall q, q = q •• nil) as Hnil. {
    intro. rewrite* field_sel_nil.
  }
  lets He1: (Hnil q). lets He2: (Hnil p).
  pose proof (pt2_exists Hp) as [? Hq].
  eapply (replacement_repl_closure_qp2_v Hi H Hq IHHp).
  rewrite He1 at 2. rewrite He2 at 2. apply rpath.
Qed.

Lemma path_sel_repl_inv_v: forall G p A T v,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢//v v : p↓A ->
    G ⊢//v v : T.
Proof.
  introv Hi Hp Hv. dependent induction Hv.
  - Case "ty_inv_r"%string.
    constructor. apply* path_sel_inv_v.
  - Case "ty_sel_r"%string.
    clear IHHv. lets Heq: (pf_pt3_unique Hi H Hp). subst*.
  - Case "ty_sel_qp_r"%string.
    destruct (repl_prefixes_sel H1) as [bs [He1 He2]].
    subst. assert (record_type (typ_rcd {A >: T <: T})) as Hrt by eauto.
    lets Hqbs: (pf_pt3_trans_inv_mult' _ Hi H Hp (or_intror Hrt)). apply* IHHv.
Qed.

Lemma invertible_typing_closure_tight_v: forall G v T U,
  inert G ->
  G ⊢//v v : T ->
  G ⊢# T <: U ->
  G ⊢//v v : U.
Proof.
  introv Hi HT Hsub.
  induction Hsub; auto.
  - dependent induction HT; eauto.
  - dependent induction HT. dependent induction H. inversion H.
  - destruct* (repl_andv Hi HT).
  - destruct* (repl_andv Hi HT).
  - dependent induction HT. dependent induction H. dependent induction H.
  - dependent induction HT. dependent induction H. dependent induction H.
  (* - admit. *)
  (* - admit. *)
  - pose proof (pt2_exists H0) as [? ?]. apply* replacement_repl_closure_pq3_v.
    (* repl closure for vals *)
  - pose proof (pt2_exists H0) as [? ?]. apply* replacement_repl_closure_qp3_v.
    (* repl closure for vals *)
  - apply* path_sel_repl_v.
  - apply* path_sel_repl_inv_v.
  - dependent induction HT. constructor*.
Qed.

Lemma replacement_closure_v : forall G v T,
    inert G ->
    G ⊢# trm_val v : T ->
    G ⊢//v v : T.
Proof.
  introv Hi Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hi eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.

Lemma repl_to_invertible_obj G U v :
  inert G ->
  G ⊢//v v : μ U ->
  exists U', G ⊢##v v : μ U' /\ G ⊢ U ⟿ U'.
Proof.
  intros Hi Hv. dependent induction Hv.
  - exists U. split*. constructor.
  - specialize (IHHv _ Hi eq_refl) as [U' [Hinv Hrc]].
    eexists. split.
    * eauto.
    * eapply star_trans. apply Hrc. apply star_one. econstructor. repeat eexists.
      apply H. eauto. eauto.
Qed.
