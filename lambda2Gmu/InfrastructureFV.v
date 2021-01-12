Set Implicit Arguments.
Require Import Prelude.
Require Import TLC.LibLogic.
Require Import TLC.LibLN.

Lemma fv_fold_general : forall A x (ls : list A) (P : A -> fset var) base,
    x \notin List.fold_left (fun (fv : fset var) (e : A) => fv \u P e) ls base ->
    x \notin base.
  induction ls.
  - introv Hfold. cbn in Hfold. auto.
  - introv Hfold. cbn in Hfold.
    assert (x \notin base \u P a).
    + apply* IHls.
    + auto.
Qed.

Lemma fv_fold_base : forall x ls base,
    x \notin List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) ls base ->
    x \notin base.
  lets*: fv_fold_general.
Qed.

Lemma fv_fold_base_clause : forall Z ls base,
    Z \notin List.fold_left (fun (fv : fset var) (cl : Clause) => fv \u fv_trm (clauseTerm cl)) ls base ->
    Z \notin base.
  intros.
  lets*: fv_fold_general (fun cl => fv_trm (clauseTerm cl)).
Qed.

Lemma fv_fold_in_general : forall A Z (e : A) (P : A -> fset var) ls base,
    Z \notin List.fold_left (fun (fv : fset var) (e' : A) => fv \u P e') ls base ->
    List.In e ls ->
    Z \notin P e.
  induction ls; introv ZIL Lin.
  - false*.
  - apply List.in_inv in Lin.
    destruct Lin.
    + cbn in ZIL.
      apply fv_fold_general in ZIL. subst. auto.
    + apply* IHls.
Qed.

Lemma fv_fold_in_clause : forall Z cl ls base,
    Z \notin List.fold_left (fun (fv : fset var) (cl : Clause) => fv \u fv_trm (clauseTerm cl)) ls base ->
    List.In cl ls ->
    Z \notin fv_trm (clauseTerm cl).
  intros.
  lets*: fv_fold_in_general (fun cl => fv_trm (clauseTerm cl)) ls.
Qed.

Lemma fv_fold_in : forall Z x ls base,
    Z \notin List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) ls base ->
    List.In x ls ->
    Z \notin fv_typ x.
  lets*: fv_fold_in_general.
Qed.

Lemma notin_fold : forall A B (ls : list A) z x (P : A -> fset B),
    (forall e, List.In e ls -> x \notin P e) ->
    x \notin z ->
    x \notin List.fold_left (fun fv e => fv \u P e) ls z.
  induction ls; introv FPe Fz; cbn; eauto.
  apply* IHls.
  - eauto with listin.
  - rewrite notin_union; split*.
    eauto with listin.
Qed.

Hint Resolve fv_fold_base fv_fold_in fv_fold_general fv_fold_in_general.

Lemma fv_open : forall T U k,
    fv_typ (open_tt_rec k U T) = (fv_typ T \u fv_typ U)
    \/ fv_typ (open_tt_rec k U T) = fv_typ T.
  induction T using typ_ind'; introv;
    try solve [
          unfold open_tt_rec; crush_compare; cbn; eauto using union_empty_l
        | cbn; eauto
        | cbn; fold (open_tt T1 U); fold (open_tt T2 U);
          rewrite union_distribute;
          apply* subset_union_2
        ].
  - cbn.
    lets* IH1: IHT1 U k.
    lets* IH2: IHT2 U k.
    destruct IH1 as [IH1 | IH1];
      destruct IH2 as [IH2 | IH2];
      rewrite IH1; rewrite IH2; eauto.
    + left.
      lets*: union_distribute.
    + left.
      rewrite <- union_assoc.
      rewrite <- union_assoc.
      rewrite (union_comm (fv_typ T2) (fv_typ U)).
      trivial.
    + rewrite union_assoc. eauto.
  - cbn.
    lets* IH1: IHT1 U k.
    lets* IH2: IHT2 U k.
    destruct IH1 as [IH1 | IH1];
      destruct IH2 as [IH2 | IH2];
      rewrite IH1; rewrite IH2; eauto.
    + left. eauto using union_distribute.
    + left.
      rewrite <- union_assoc.
      rewrite <- union_assoc.
      rewrite (union_comm (fv_typ T2) (fv_typ U)).
      trivial.
    + rewrite union_assoc. eauto.
  - cbn.
    induction ls.
    + cbn. eauto.
    + assert (Has: List.Forall
           (fun T : typ =>
            forall (U : typ) (k : nat),
            fv_typ (open_tt_rec k U T) = fv_typ T \u fv_typ U \/
            fv_typ (open_tt_rec k U T) = fv_typ T) ls).
      * rewrite List.Forall_forall in *.
        eauto with listin.
      * lets* IH: IHls Has.
        destruct IH as [IH | IH].
        -- left.
           cbn.
           repeat rewrite union_fold_detach in *.
           rewrite IH.
           rewrite <- union_assoc.
           rewrite List.Forall_forall in *.
           lets* Ha: H a U k; eauto with listin.
           destruct Ha as [Ha | Ha].
           ++ rewrite union_distribute.
              rewrite union_assoc.
              f_equal. eauto.
           ++ rewrite <- union_assoc.
              rewrite (union_comm (fv_typ a) (fv_typ U)).
              f_equal. f_equal. eauto.
        -- rewrite List.Forall_forall in *.
           lets* Ha: H a U k; eauto with listin.
           destruct Ha as [Ha | Ha].
           ++ left.
              cbn.
              repeat rewrite union_fold_detach.
              rewrite IH.
              rewrite <- union_assoc.
              f_equal. eauto.
           ++ right.
              cbn.
              repeat rewrite union_fold_detach.
              f_equal; eauto.
Qed.

Lemma fv_smaller : forall T U k,
    fv_typ (open_tt_rec k U T) \c (fv_typ T \u fv_typ U).
  introv.
  lets* characterized: fv_open T U k.
  destruct characterized as [Hc | Hc]; rewrite Hc; eauto.
Qed.

Lemma fv_typs_notin : forall Ts T X,
    List.In T Ts ->
    X \notin fv_typs Ts ->
    X \notin fv_typ T.
  introv Hin Hall.
  induction Ts as [| Th Tt].
  - inversion Hin.
  - lets* Hem: (classicT (Th = T)).
    destruct Hem.
    + subst.
      cbn in Hall.
      eauto.
    + inversion Hin.
      * contradiction.
      * apply* IHTt.
        cbn in Hall. eauto.
Qed.

Lemma notin_fv_tt_open : forall Y X T,
    X \notin fv_typ (T open_tt_var Y) ->
    X \notin fv_typ T.
Proof.
  unfold open_tt.
  introv FO.
  lets* characterized: fv_open T (typ_fvar Y) 0.
  destruct characterized as [Hc | Hc]; rewrite Hc in FO; eauto.
Qed.

Lemma fv_smaller_many : forall As T,
    fv_typ (open_tt_many_var As T) \c (fv_typ T \u from_list As).
  induction As as [| Ah Ats]; introv.
  - cbn. eauto.
  - cbn.
    fold (from_list Ats).
    fold (open_tt_many_var Ats (T open_tt_var Ah)).
    lets IH: IHAts (T open_tt_var Ah).
    intros x xin.
    lets Hin: IH xin.
    rewrite in_union in Hin.
    rewrite union_assoc.
    destruct Hin as [Hin | Hin].
    + lets Hs: fv_smaller T (typ_fvar Ah) 0.
      fold (open_tt T (typ_fvar Ah)) in Hs.
      lets Hf: Hs Hin. cbn in Hf.
      rewrite* in_union.
    + rewrite* in_union.
Qed.

Lemma fv_open_tt : forall x T1 T2 k,
    x \notin fv_typ T1 ->
    x \notin fv_typ T2 ->
    x \notin fv_typ (open_tt_rec k T1 T2).
  introv f1 f2.
  unfold open_tt.
  lets [Ho | Ho]: fv_open T2 T1 k; rewrite Ho; eauto.
Qed.

Lemma fv_open_te : forall e k x T,
    x \notin fv_trm e ->
    x \notin fv_typ T ->
    x \notin fv_trm (open_te_rec k T e).
  induction e using trm_ind'; introv efresh Tfresh;
    try solve [
          cbn in *; eauto
        | cbn in *;
          rewrite notin_union;
          split*; apply* fv_open_tt
        ].
  - cbn. cbn in efresh.
    apply notin_fold.
    + intros T' Tin.
      unfold open_typlist_rec in Tin.
      lets Tin2: Tin.
      apply List.in_map_iff in Tin2.
      destruct Tin2 as [T'' [T'eq T''in]].
      subst.
      apply* fv_open_tt.
    + apply* IHe.
  - cbn in *.
    apply notin_fold.
    + intros cl clin.
      apply List.in_map_iff in clin.
      destruct clin as [[cl'A cl'T] [cl'eq cl'in]].
      subst. cbn.

      rewrite List.Forall_forall in *.
      fold (clauseTerm (clause cl'A cl'T)).
      apply* H.

      cbn.
      fold (clauseTerm (clause cl'A cl'T)).
      apply* fv_fold_in_clause.
    + apply* IHe.
      apply* fv_fold_base_clause.
Qed.

Lemma fv_open_te_many : forall Ts e x,
    (forall T, List.In T Ts -> x \notin fv_typ T) ->
    x \notin fv_trm e ->
    x \notin fv_trm (open_te_many Ts e).
  induction Ts as [| Th Tts]; introv Tfresh efresh.
  - cbn. trivial.
  - cbn. apply IHTts.
    + introv Tin. eauto with listin.
    + unfold open_te.
      apply fv_open_te; eauto with listin.
Qed.

Lemma fv_env_extend : forall E x T,
    fv_env (E & x ~: T) = fv_typ T \u fv_env E.
  intros.
  rewrite concat_def.
  rewrite single_def.
  cbn.
  fold (fv_env E).
  trivial.
Qed.

Lemma notin_env_inv : forall E X x T,
    X \notin fv_env (E & x ~: T) ->
    X \notin fv_env E /\ X \notin fv_typ T.
  introv Fr.
  rewrite fv_env_extend in Fr.
  rewrite* notin_union in Fr.
Qed.

Lemma notin_domΔ_eq : forall D1 D2 X,
    X \notin domΔ (D1 |,| D2) <->
    X \notin domΔ D1 /\ X \notin domΔ D2.
  induction D1; intros; constructor;
    try solve [cbn in *; intuition]; intro H;
      destruct a; cbn in *;
        repeat rewrite notin_union in *;
        destruct (IHD1 D2 X) as [IH1 IH2];
        intuition.
Qed.

Lemma fold_empty : forall Ts,
    (forall T : typ, List.In T Ts -> fv_typ T = \{}) ->
    List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) Ts \{} = \{}.
  induction Ts as [ | Th]; introv Fv; cbn; eauto.
  lets* Hempty: Fv Th.
  rewrite Hempty; eauto with listin.
  rewrite union_empty_r.
  eauto with listin.
Qed.

Lemma in_fold_exists : forall TV TT P ls Z X,
    X \in List.fold_left (fun (fv : fset TV) (T : TT) => fv \u P T) ls Z ->
          (exists T, List.In T ls /\ X \in P T) \/ X \in Z.
  induction ls; introv Hin.
  - right.
    cbn in *. eauto.
  - cbn in Hin.
    lets* IH: IHls (Z \u P a) X Hin.
    destruct IH as [IH | IH].
    + destruct IH as [T [Tin PT]].
      left. exists T. eauto with listin.
    + rewrite in_union in IH.
      destruct IH as [IH | IH]; eauto with listin.
Qed.

Lemma fv_subst_tt : forall X Z P T,
    X \notin fv_typ T ->
    X \notin fv_typ P ->
    X \notin fv_typ (subst_tt Z P T).
  induction T using typ_ind'; introv FT FP; cbn in *; auto.
  - case_if*.
  - apply notin_fold.
    + intros T Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [U [? ?]]. subst.
      rewrite List.Forall_forall in H.
      apply* H.
    + auto.
Qed.

Lemma fv_env_subst : forall X Z P E,
    X \notin fv_env E ->
    X \notin fv_typ P ->
    X \notin fv_env (map (subst_tb Z P) E).
  intros.
  induction E using env_ind.
  - rewrite map_empty. auto.
  - destruct v as [T]; lets [? ?]: notin_env_inv H.
    rewrite map_concat.
    rewrite map_single.
    cbn.
    rewrite fv_env_extend.
    rewrite notin_union.
    split.
    + apply* fv_subst_tt.
    + apply* IHE.
Qed.
