Set Implicit Arguments.
Require Import Prelude.
Require Import TLC.LibLogic.
Require Import TLC.LibLN.
(* large portions of this are based on the TLC formalisation of FSub *)

(** * Infrastructure *)
(**
   Defines lemmas related to handling variables: opening, substitution, free variables.
*)

(** ** Preserving size *)
Lemma open_ee_var_preserves_size : forall e x n,
    trm_size e = trm_size (open_ee_rec n (trm_fvar x) e).
  induction e using trm_ind'; introv; try solve [cbn; try case_if; cbn; eauto].
  cbn.
  - rewrite <- IHe.
    f_equal.
    f_equal.
    unfold map_clause_trms.
    rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H cl clin.
    destruct cl.
    unfold clauseTerm.
    apply* Heq.
Qed.

Lemma open_te_var_preserves_size : forall e x n,
    trm_size e = trm_size (open_te_rec n (typ_fvar x) e).
  induction e using trm_ind'; introv; try solve [cbn; try case_if; cbn; eauto].
  - cbn.
    rewrite <- IHe.
    f_equal.
    f_equal.
    unfold map_clause_trms.
    rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H cl clin.
    destruct cl.
    unfold clauseTerm.
    apply* Heq.
Qed.

Lemma open_tt_var_preserves_size : forall T X n,
    typ_size T = typ_size (open_tt_rec n (typ_fvar X) T).
  induction T using typ_ind' ; introv; try solve [cbn; try case_if; cbn; eauto].
  - cbn. crush_compare.
  - cbn.
    rewrite List.map_map.
    assert ((List.map typ_size ls) = (List.map (fun x : typ => typ_size (open_tt_rec n0 (typ_fvar X) x)) ls)) as Hmapeq.
    + apply List.map_ext_in.
      rewrite List.Forall_forall in H.
      intros. apply* H.
    + rewrite Hmapeq. auto.
Qed.

(** ** Properties of type substitution in type *)

(** Substitution on indices is identity on well-formed terms. *)

Inductive typ_closed_in_surroundings : nat -> typ -> Prop :=
| closed_typ_bvar : forall J k, J < k -> typ_closed_in_surroundings k (typ_bvar J)
| closed_typ_fvar : forall X k, typ_closed_in_surroundings k (typ_fvar X)
| closed_typ_unit : forall k, typ_closed_in_surroundings k (typ_unit)
| closed_typ_tuple : forall T1 T2 k,
    typ_closed_in_surroundings k T1 ->
    typ_closed_in_surroundings k T2 ->
    typ_closed_in_surroundings k (T1 ** T2)
| closed_typ_arrow : forall T1 T2 k,
    typ_closed_in_surroundings k T1 ->
    typ_closed_in_surroundings k T2 ->
    typ_closed_in_surroundings k (T1 ==> T2)
| closed_typ_all : forall T k,
    typ_closed_in_surroundings (S k) T ->
    typ_closed_in_surroundings k (typ_all T)
| closed_typ_gadt : forall Ts N k,
    List.Forall (typ_closed_in_surroundings k) Ts ->
    typ_closed_in_surroundings k (typ_gadt Ts N).

Lemma opening_adds_one : forall T X k n,
    typ_closed_in_surroundings n (open_tt_rec k (typ_fvar X) T) ->
    typ_closed_in_surroundings (max (S n) (S k)) T.
  induction T using typ_ind'; introv Hc; try solve [inversions Hc; constructor*].
  - cbn in Hc.
    crush_compare; cbn in *; econstructor; try lia.
    inversions Hc. lia.
  - econstructor.
    cbn in *.
    inversions Hc.
    lets* IH: IHT X (S k) (S n).
  - constructor*.
    inversions Hc.
    rewrite List.Forall_forall in *.
    intros T Hin.
    lets* IH: H T Hin X k n0.
    apply* IH.
    apply* H2.
    apply* List.in_map.
Qed.

Lemma type_closed : forall T,
    type T -> typ_closed_in_surroundings 0 T.
  induction 1; constructor*.
  - pick_fresh X.
    lets* Hoao: opening_adds_one T2 X 0 0.
  - rewrite List.Forall_forall.
    auto.
Qed.

Lemma closed_id : forall T U n k,
    typ_closed_in_surroundings n T ->
    k >= n ->
    T = open_tt_rec k U T.
  induction T using typ_ind'; introv Hc Hk; eauto;
    try solve [
          cbn; crush_compare; inversions Hc; lia
        | cbn; inversions Hc;
          lets* IH1: IHT1 U n k;
          lets* IH2: IHT2 U n k;
          rewrite* <- IH1;
          rewrite* <- IH2
          ].
  - lets* IH: IHT U (S n) (S k).
    cbn. inversions Hc.
    rewrite* <- IH. lia.
  - cbn.
    f_equal.
    inversions Hc.
    rewrite List.Forall_forall in *.
    rewrite <- List.map_id at 1.
    apply List.map_ext_in.
    intros T Hin.
    lets* IH: H Hin.
Qed.

Lemma open_tt_rec_type : forall T U,
  type T -> forall k, T = open_tt_rec k U T.
Proof.
  introv Htype. intros.
  lets* Hc: closed_id T U 0 k.
  apply Hc.
  - apply* type_closed.
  - lia.
Qed.


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

Hint Resolve fv_fold_base fv_fold_in fv_fold_general fv_fold_in_general.

Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_typ T -> subst_tt Z U T = T.
Proof.
  induction T using typ_ind' ; simpl; intros; f_equal*.
  - case_var*.
  - symmetry.
    apply map_id.
    introv Lin.
    handleforall.
    symmetry.
    apply* Hforall.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P n, type P ->
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1).
Proof.
  introv WP. generalize n.
  induction T1 using typ_ind' ; intros k; simpls; f_equal*.
  - crush_compare.
  - case_var*. rewrite* <- open_tt_rec_type.
  - rewrite* List.map_map.
    rewrite* List.map_map.
    apply List.map_ext_in.
    handleforall.
    introv Lin.
    apply* Hforall.
Qed.

Lemma subst_tt_open_tt : forall T1 T2 X P, type P ->
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof.
  unfold open_tt. autos* subst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_tt_open_tt_var : forall X Y U T, Y <> X -> type U ->
  (subst_tt X U T) open_tt_var Y = subst_tt X U (T open_tt_var Y).
Proof.
  introv Neq Wu. rewrite* subst_tt_open_tt.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_tt_intro : forall X T2 U,
  X \notin fv_typ T2 -> type U ->
  open_tt T2 U = subst_tt X U (T2 open_tt_var X).
Proof.
  introv Fr Wu. rewrite* subst_tt_open_tt.
  rewrite* subst_tt_fresh. simpl. case_var*.
Qed.

(* possibly move to Defs *)
Fixpoint subst_tt_many (Xs : list var) (Us : list typ) (T : typ) :=
  match (Xs, Us) with
  (* | ((List.cons X Xt), (List.cons U Ut)) => subst_tt X U (subst_tt_many Xt Ut T) *)
  | ((List.cons X Xt), (List.cons U Ut)) => subst_tt_many Xt Ut (subst_tt X U T)
  | _ => T
  end.

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

Lemma subst_commutes_with_unrelated_opens : forall Xs T V Y,
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    subst_tt Y V (open_tt_many_var Xs T) =
    (open_tt_many_var Xs (subst_tt Y V T)).
  induction Xs as [| Xh Xt]; introv Hneq Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_tt_many_var Xt (T open_tt_var Xh)).
    fold (open_tt_many_var Xt (subst_tt Y V T open_tt_var Xh)).
    rewrite* subst_tt_open_tt_var; eauto with listin.
Qed.

Lemma subst_intro_commutes_opens : forall Xs T Y V,
    Y \notin fv_typ T ->
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    open_tt_many_var Xs (open_tt T V) =
    subst_tt Y V (open_tt_many_var Xs (T open_tt_var Y)).
  induction Xs as [| Xh Xt]; introv Hfv Hneq Htyp.
  - cbn. apply* subst_tt_intro.
  - cbn.
    fold (open_tt_many_var Xt (open_tt T V open_tt_var Xh)).
    fold (open_tt_many_var Xt ((T open_tt_var Y) open_tt_var Xh)).
    rewrite* subst_commutes_with_unrelated_opens.
    f_equal.
    rewrite* <- subst_tt_open_tt_var.
    + rewrite* <- subst_tt_intro.
    + apply* Hneq. cbn; eauto.
    + eauto with listin.
Qed.

Lemma sublist_tail_prop : forall A (Uh : A) (Ut : list A) (P : A -> Prop),
  (forall U : A, List.In U (Uh :: Ut) -> P U) ->
  forall U : A, List.In U Ut -> P U.
  introv Hbigger Hin.
  apply* Hbigger.
  cbn.
  eauto.
Qed.

Lemma sublist_head_prop : forall A (Uh : A) (Ut : list A) (P : A -> Prop),
  (forall U : A, List.In U (Uh :: Ut) -> P U) ->
  P Uh.
  introv Hbigger.
  apply* Hbigger.
  cbn.
  eauto.
Qed.

Lemma subst_tt_intro_many : forall Xs T Us,
    length Xs = length Us ->
    DistinctList Xs ->
    (forall X, List.In X Xs -> X \notin fv_typ T) ->
    (forall X U, List.In X Xs -> List.In U Us -> X \notin fv_typ U) ->
    (forall U, List.In U Us -> type U) ->
    open_tt_many Us T = subst_tt_many Xs Us (open_tt_many_var Xs T).
  induction Xs as [| Xh Xt]; introv Hleneq Hdistinct HXfv HXUfv XUtyp.
  - destruct Us.
    + cbv. trivial.
    + inversions Hleneq.
  - destruct Us as [| Uh Ut].
    + inversions Hleneq.
    + cbn.
      fold (open_tt_many_var Xt (T open_tt_var Xh)).
      rewrite* <- subst_intro_commutes_opens; eauto with listin.
      * apply* IHXt; try solve [intuition; eauto with listin].
        -- inversion* Hdistinct.
        -- introv XiXt.
           lets* Hless: fv_smaller T Uh 0.
           fold (open_tt T Uh) in Hless.
           intro Hin.
           apply Hless in Hin.
           rewrite in_union in Hin.
           destruct Hin as [Hin | Hin].
           ++ apply* HXfv. listin.
           ++ apply* HXUfv; listin.
      * inversions Hdistinct.
        introv XiXt.
        intro. subst. contradiction.
Qed.

(* ********************************************************************** *)
(** ** Properties of type substitution in terms *)

Lemma open_te_rec_term_core : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof.
  induction e using trm_ind';
    try solve [intros; simpl in *; inversion H; f_equal*; f_equal*].
  introv Heq.
  - rewrite List.Forall_forall in *.
    cbn. cbn in Heq.
    f_equal;
      inversion* Heq.
    rewrite <- (List.map_id) at 1.
    apply* List.map_ext_in.
    intros cl clin.
    rewrite List.map_map in H2.
    lets Heqcl: ext_in_map H2 clin.
    destruct cl.
    lets* IH: H clin (S j) u (i + clArity) P.
    cbn in IH.
    f_equal.
    apply* IH.
    inversion* Heqcl.
Qed.

(* this one describes terms being closed in relation to type-variables, not term-varaibles*)
Inductive te_closed_in_surroundings : nat -> trm -> Prop :=
| closed_trm_bvar : forall i k, te_closed_in_surroundings k (trm_bvar i)
| closed_trm_fvar : forall x k, te_closed_in_surroundings k (trm_fvar x)
| closed_trm_unit : forall k, te_closed_in_surroundings k (trm_unit)
| closed_trm_fst : forall e k, te_closed_in_surroundings k e -> te_closed_in_surroundings k (trm_fst e)
| closed_trm_snd : forall e k, te_closed_in_surroundings k e -> te_closed_in_surroundings k (trm_snd e)
| closed_trm_tuple : forall e1 e2 k, te_closed_in_surroundings k e1 ->
                                te_closed_in_surroundings k e2 ->
                                te_closed_in_surroundings k (trm_tuple e1 e2)
| closed_trm_abs : forall e T k, te_closed_in_surroundings k e ->
                            typ_closed_in_surroundings k T ->
                            te_closed_in_surroundings k (trm_abs T e)
| closed_trm_app : forall e1 e2 k, te_closed_in_surroundings k e1 ->
                              te_closed_in_surroundings k e2 ->
                              te_closed_in_surroundings k (trm_app e1 e2)
| closed_trm_tabs : forall e k, te_closed_in_surroundings (S k) e ->
                           te_closed_in_surroundings k (trm_tabs e)
| closed_trm_tapp : forall e T k, te_closed_in_surroundings k e ->
                            typ_closed_in_surroundings k T ->
                            te_closed_in_surroundings k (trm_tapp e T)
| closed_trm_fix : forall e T k, te_closed_in_surroundings k e ->
                            typ_closed_in_surroundings k T ->
                            te_closed_in_surroundings k (trm_fix T e)
| closed_trm_let : forall e1 e2 k, te_closed_in_surroundings k e1 ->
                              te_closed_in_surroundings k e2 ->
                              te_closed_in_surroundings k (trm_let e1 e2)
| closed_term_constructor : forall Ts N e k,
    List.Forall (typ_closed_in_surroundings k) Ts ->
    te_closed_in_surroundings k e ->
    te_closed_in_surroundings k (trm_constructor Ts N e)
| closed_term_match : forall G e ms k,
    te_closed_in_surroundings k e ->
    (forall cl, List.In cl ms -> te_closed_in_surroundings (k + clauseArity cl) (clauseTerm cl)) ->
    te_closed_in_surroundings k (trm_matchgadt e G ms)
.

Lemma te_opening_te_adds_one : forall e X k n,
    te_closed_in_surroundings n (open_te_rec k (typ_fvar X) e) ->
    te_closed_in_surroundings (max (S n) (S k)) e.
  induction e using trm_ind'; introv Hc; inversions Hc;
    try solve [
          constructor*
        | constructor*; apply* opening_adds_one
        ].
  - constructor*.
    rewrite List.Forall_forall in *.
    intros T Hin.
    apply* opening_adds_one.
    apply* H2.
    unfold open_typlist_rec.
    apply* List.in_map.
  - econstructor. apply* IHe.
  - constructor*.
    introv clin.
    rewrite List.Forall_forall in *.
    lets* IHcl: H clin.
    destruct cl as [clArity clTerm].
    cbn.
    cbn in IHcl.
    assert (Harit: Nat.max n k + clArity = Nat.max (n + clArity) (k + clArity)); try lia.
    rewrite Harit.
    apply IHcl with X.
    lets* IHcl2: H5 (clause clArity (open_te_rec (k + clArity) (typ_fvar X) clTerm)).
    cbn in IHcl2.
    apply* IHcl2.
    apply* List.in_map_iff.
    exists (clause clArity clTerm). eauto.
Qed.

Lemma te_opening_ee_preserves : forall e x k n,
    te_closed_in_surroundings n (open_ee_rec k (trm_fvar x) e) ->
    te_closed_in_surroundings n e.
  induction e using trm_ind'; introv Hc; try solve [inversions Hc; constructor*].
  - inversions Hc.
    rewrite List.Forall_forall in *.
    constructor*.
    introv clin.
    apply H with x (S k); eauto.
    destruct cl as [clA clT].
    lets* Hcl: H5 (clause clA (open_ee_rec (S k) (trm_fvar x) clT)).
    cbn in Hcl.
    cbn.
    apply Hcl.
    apply* List.in_map_iff.
    exists (clause clA clT). eauto.
Qed.

Lemma te_opening_te_many_adds : forall As N n e,
    te_closed_in_surroundings n (open_te_many_var As e) ->
    length As = N ->
    te_closed_in_surroundings (N + n) e.
  induction As as [| Ah Ats]; destruct N; introv Hcl Hlen; inversion Hlen.
  - cbn in *. eauto.
  - cbn in Hcl.
    fold (open_te_many_var Ats (e open_te_var Ah)) in Hcl.

    lets IH: IHAts (length Ats) n (e open_te_var Ah).
    assert (Harit2: Nat.max (S (length Ats + n)) (S 0) = (S (length Ats) + n)); try lia.
    rewrite <- Harit2.
    apply te_opening_te_adds_one with Ah.
    fold (e open_te_var Ah).
    apply* IH.
Qed.

Lemma term_te_closed : forall e,
    term e -> te_closed_in_surroundings 0 e.
  induction 1; try solve [
                     constructor*
                   | match goal with
                     | H: forall x : var, x \notin ?L ->
                                     te_closed_in_surroundings 0 (?e1 open_ee_var x)
                                     |- _ =>
                       constructor*; try solve [
                                           pick_fresh X; apply* te_opening_ee_preserves; lets* He: H X
                                         | apply* type_closed]
                     end
                   ].
  - constructor*.
    rewrite List.Forall_forall. intros T Hin.
    apply* type_closed.
  - constructor*.
    pick_fresh X.
    lets* Hopen: te_opening_te_adds_one e1 X 0 0.
  - constructor*. apply* type_closed.
  - constructor*.
    introv clin.
    cbn.
    lets* fresh_alphas: exist_alphas L (clauseArity cl).
    inversion fresh_alphas as [Alphas [Hlen [Hdist Hnotin]]].
    rewrite length_equality in Hlen.
    pick_fresh x.
    assert (xfresh: x \notin L); eauto.
    assert (xfreshA: x \notin from_list Alphas); eauto.
    lets hmm: H1 clin Alphas x Hlen Hdist.
    lets hmm2: hmm Hnotin xfresh xfreshA.
    unfold open_ee in hmm2.
    lets hmm3: te_opening_ee_preserves hmm2.
    lets hmm4: te_opening_te_many_adds (clauseArity cl) hmm3.
    assert (Hneutral: forall n, n + 0 = n); try (intro; lia).
    rewrite Hneutral in hmm4.
    apply* hmm4.
Qed.

Lemma te_closed_id : forall e T n k,
    te_closed_in_surroundings n e ->
    k >= n ->
    e = open_te_rec k T e.
  induction e using trm_ind'; introv Hc Hk; eauto; inversions Hc; cbn; f_equal;
    try (match goal with
         | IH: forall T n k, ?P1 -> ?P2 -> ?e1 = open_te_rec k T ?e1 |- _ => apply* IH
         end);
    try apply* closed_id;
    try lia.
  - unfold open_typlist_rec.
    rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intro U.
    rewrite List.Forall_forall in *.
    lets* HC: H2 U.
    lets*: closed_id U T n k.
  - rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    destruct cl as [clA clT].
    f_equal.
    lets* IH: H (clause clA clT) T (n + clA) (k + clA).
    cbn in IH.
    apply* IH.
    + lets* Hcl: H5 (clause clA clT).
    + lia.
Qed.

Lemma open_te_rec_term : forall e U,
  term e -> forall k, e = open_te_rec k U e.
Proof.
  introv Hterm. intros.
  lets* Hc: te_closed_id e U 0 k.
  apply Hc.
  - apply* term_te_closed.
  - lia.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_te_fresh : forall X U e,
  X \notin fv_trm e -> subst_te X U e = e.
Proof.
  induction e using trm_ind'; simpl; intros; f_equal*; autos* subst_tt_fresh.
  - symmetry.
    apply map_id. introv Lin.
    symmetry.
    apply* subst_tt_fresh.
  - apply* IHe.
    lets*: fv_fold_general H0.
  - unfold map_clause_trm_trm.
    rewrite List.Forall_forall in *.
    rewrite <- List.map_id.
    apply List.map_ext_in.
    intros cl clin.
    lets* Heq: H cl clin.
    destruct cl.
    f_equal.
    apply* Heq.
    lets*: fv_fold_in_clause.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_te_open_te : forall e T X U, type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T).
Proof.
  intros. unfold open_te. generalize 0.
  induction e using trm_ind'; intro n0; simpls; f_equal*;
    autos* subst_tt_open_tt_rec.
  - unfold open_typlist_rec.
    rewrite List.map_map.
    rewrite List.map_map.
    apply List.map_ext.
    intro.
    apply* H0.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H0 cl clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_te_open_te_var : forall X Y U e, Y <> X -> type U ->
  (subst_te X U e) open_te_var Y = subst_te X U (e open_te_var Y).
Proof.
  introv Neq Wu. rewrite* subst_te_open_te.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_te_intro : forall X U e,
  X \notin fv_trm e -> type U ->
  open_te e U = subst_te X U (e open_te_var X).
Proof.
  introv Fr Wu. rewrite* subst_te_open_te.
  rewrite* subst_te_fresh. simpl. case_var*.
Qed.

(** ** Properties of term substitution in terms *)
Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e using trm_ind'; introv Neq Hopen; simpl in *; inversion Hopen; f_equal*.
  - crush_eq. crush_eq. subst. intuition.
  - rewrite List.Forall_forall in *.
    rewrite List.map_map in H2.
    rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intros cl clin.
    lets* Hcleq: ext_in_map H2 clin.
    destruct cl.
    inversion* Hcleq.
    f_equal.
    lets* IH: H clin (S j) (S i).
Qed.

Lemma open_ee_rec_type_core : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e using trm_ind'; introv Ho; simpls; inversion Ho; f_equal*.
  - rewrite List.Forall_forall in *.
    rewrite List.map_map in H2.
    rewrite <- List.map_id at 1.
    apply* List.map_ext_in.
    intros cl clin.
    lets* Hcleq: ext_in_map H2 clin.
    destruct cl.
    inversion* Hcleq.
    f_equal.
    lets* IH: H clin (j + clArity) (S i).
Qed.

Lemma open_ee_rec_type_many : forall As k u e,
  open_te_many_var As e =
  open_ee_rec k u (open_te_many_var As e) ->
  e = open_ee_rec k u e.
  induction As as [| Ah Ats]; introv Heq.
  - cbn in Heq. eauto.
  - cbn in Heq.
    fold (open_te_many_var Ats (e open_te_var Ah)) in Heq.
    lets* IH: IHAts k u (e open_te_var Ah) Heq.
    apply* open_ee_rec_type_core.
Qed.

Lemma open_ee_rec_term : forall u e,
  term e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intro k;
    simpl; f_equal*.
  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).

  - unfolds open_te.
    pick_fresh X.
    apply* (@open_ee_rec_type_core e1 0 (typ_fvar X)).

  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core v1 0 (trm_fvar x)).

  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e2 0 (trm_fvar x)).
  - rewrite <- List.map_id at 1.
    apply List.map_ext_in.
    intros cl clin.
    destruct cl as [clA clT].
    f_equal.

    lets* fresh_alphas: exist_alphas L clA.
    inversion fresh_alphas as [Alphas [Hlen [Hdist Hnotin]]].
    rewrite length_equality in Hlen.
    pick_fresh x.
    assert (xfresh: x \notin L); eauto.


    lets* IHcl: H1 clin Alphas x.
    cbn in IHcl.
    lets* IHcl2: IHcl Hlen Hdist Hnotin xfresh.

    assert (Hpart: open_te_many_var Alphas clT =
                   open_ee_rec (S k) u (open_te_many_var Alphas clT)).
    + unfolds open_ee.
      eapply open_ee_rec_term_core.
      2: {
        apply* IHcl2.
      }
      lia.
    + apply* open_ee_rec_type_many.
Qed.

(** Substitution for a fresh name is identity. *)
Lemma subst_ee_fresh : forall x u e,
  x \notin fv_trm e -> subst_ee x u e = e.
Proof.
  induction e using trm_ind'; simpl; intros; f_equal*.
  - case_var*.
  - apply IHe.
    lets*: fv_fold_base_clause.
  - unfold map_clause_trm_trm.
    rewrite <- List.map_id.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* Heq: H clin.
    unfold clauseTerm in Heq.
    lets Hfv: fv_fold_in_clause.
    lets* Hfv2: Hfv cl clauses.
    unfold clauseTerm in Hfv2.
    destruct cl.
    f_equal.
    apply Heq.
    apply* Hfv2.
Qed.

(** Substitution distributes on the open operation. *)
Lemma subst_ee_open_ee : forall t1 t2 u x, term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1 using trm_ind'; intro n0; simpls; f_equal*.
  - crush_eq.
  - case_var*. rewrite* <- open_ee_rec_term.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* IH: H0 clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Substitution and open_var for distinct names commute. *)
Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> term u ->
  (subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_trm e -> term u ->
  open_ee e u = subst_ee x u (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Interactions between type substitutions in terms and opening
  with term variables in terms. *)

Lemma subst_te_open_ee_var : forall Z P x e,
  (subst_te Z P e) open_ee_var x = subst_te Z P (e open_ee_var x).
Proof.
  introv. unfold open_ee. generalize 0.
  induction e using trm_ind'; intros; simpl; f_equal*.
  - crush_eq.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* IH: H clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Interactions between term substitutions in terms and opening
  with type variables in terms. *)

Lemma subst_ee_open_te_var : forall z u e X, term u ->
  (subst_ee z u e) open_te_var X = subst_ee z u (e open_te_var X).
Proof.
  introv. unfold open_te. generalize 0.
  induction e using trm_ind'; intros; simpl; f_equal*.
  - case_var*. symmetry. autos* open_te_rec_term.
  - unfold map_clause_trm_trm.
    repeat rewrite List.map_map.
    apply List.map_ext_in.
    intros cl clin.
    rewrite List.Forall_forall in *.
    lets* IH: H clin.
    destruct cl.
    f_equal.
    eauto.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_map_reverse_type : forall Tparams Z P,
    type P ->
    (forall Tparam : typ,
        List.In Tparam Tparams -> type P -> type (subst_tt Z P Tparam)) ->
    forall Tparam : typ, List.In Tparam (List.map (subst_tt Z P) Tparams) -> type Tparam.
  introv HP HTP.
  introv Tin.
  apply List.in_map_iff in Tin.
  destruct Tin as [T Tand].
  destruct Tand as [Teq Tin].
  rewrite <- Teq.
  apply* HTP.
Qed.

Lemma subst_tt_type : forall T Z P,
  type T -> type P -> type (subst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  - case_var*.
  - apply_fresh* type_all as X. rewrite* subst_tt_open_tt_var.
  - econstructor.
    apply* subst_map_reverse_type.
Qed.

Lemma subst_commutes_with_unrelated_opens_te_te : forall Xs e V Y,
    (forall X, List.In X Xs -> X <> Y) ->
    type V ->
    subst_te Y V (open_te_many_var Xs e) =
    (open_te_many_var Xs (subst_te Y V e)).
  induction Xs as [| Xh Xt]; introv Hneq Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_te_many_var Xt (e open_te_var Xh)).
    fold (open_te_many_var Xt (subst_te Y V e open_te_var Xh)).
    rewrite* subst_te_open_te_var; eauto with listin.
Qed.

Lemma subst_commutes_with_unrelated_opens_te_ee : forall Xs e v y,
    (forall X, List.In X Xs -> X <> y) ->
    term v ->
    subst_ee y v (open_te_many_var Xs e) =
    (open_te_many_var Xs (subst_ee y v e)).
  induction Xs as [| Xh Xt]; introv Hneq Htyp.
  - cbn. eauto.
  - cbn.
    fold (open_te_many_var Xt (e open_te_var Xh)).
    fold (open_te_many_var Xt (subst_ee y v e open_te_var Xh)).
    rewrite* subst_ee_open_te_var; eauto with listin.
Qed.

Lemma subst_te_term : forall e Z P,
    term e -> type P -> term (subst_te Z P e)
with subst_te_value : forall e Z P,
    value e -> type P -> value (subst_te Z P e).
Proof.
  - lets: subst_tt_type. induction 1; intros; cbn; auto.
    + constructor*.
      apply* subst_map_reverse_type.
    + apply_fresh* term_abs as x. rewrite* subst_te_open_ee_var.
    + apply_fresh* term_tabs as x.
      rewrite* subst_te_open_te_var.
      rewrite* subst_te_open_te_var.
    + apply_fresh* term_fix as x.
      rewrite* subst_te_open_ee_var.
      rewrite* subst_te_open_ee_var.
    + apply_fresh* term_let as x. rewrite* subst_te_open_ee_var.
    + econstructor; eauto.
      intros cl clinmap Alphas x Hlen Hdist Afresh xfresh xfreshA.
      destruct cl as [clA clT].
      unfold map_clause_trm_trm in clinmap.
      lets cl2: clinmap.
      apply List.in_map_iff in cl2.
      destruct cl2 as [[cl'A cl'T] [cl'eq cl'in]].
      inversion cl'eq. subst.
      cbn.
      lets* IH: H2 cl'in Alphas x Hlen Hdist.
      cbn in IH.
      instantiate (1:=(L \u \{ Z })) in Afresh.
      assert (Hpull:
          open_te_many_var Alphas (subst_te Z P cl'T) open_ee_var x
          =
          subst_te Z P (open_te_many_var Alphas cl'T open_ee_var x)
        ).
      * rewrite <- subst_commutes_with_unrelated_opens_te_te.
        rewrite* subst_te_open_ee_var.
        -- intros A AAlpha.
           assert (A \notin L \u \{ Z }); solve [apply* Afresh | eauto].
        -- eauto.
      * rewrite Hpull.
        apply* IH.
        introv Ain.
        assert (A \notin L \u \{ Z}); eauto.
  - lets: subst_tt_type; induction 1; intros; cbn; auto;
      match goal with
      | H: term _ |- _ => rename H into Hterm end.
    + apply value_abs.
      inversions Hterm.
      apply_fresh* term_abs as x.
      rewrite* subst_te_open_ee_var.
    + apply value_tabs. inversion Hterm.
      apply_fresh* term_tabs as x.
      rewrite* subst_te_open_te_var.
      rewrite* subst_te_open_te_var.
    + constructor*.
      constructor*.
      * apply* value_is_term.
      * apply* subst_map_reverse_type.
        inversion* Hterm.
Qed.

Lemma subst_ee_term : forall e1 Z e2,
    term e1 -> term e2 -> term (subst_ee Z e2 e1)
with subst_ee_value : forall e1 Z e2,
    value e1 -> term e2 -> value (subst_ee Z e2 e1).
Proof.
  - induction 1; intros; simpl; auto.
    + case_var*.
    + apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
    + apply_fresh* term_tabs as Y; rewrite* subst_ee_open_te_var.
    + apply_fresh* term_fix as y; rewrite* subst_ee_open_ee_var.
    + apply_fresh* term_let as y. rewrite* subst_ee_open_ee_var.
    + econstructor; eauto.
      intros cl clinmap Alphas x Hlen Hdist Afresh xfresh xfreshA.
      destruct cl as [clA clT].
      unfold map_clause_trm_trm in clinmap.
      lets cl2: clinmap.
      apply List.in_map_iff in cl2.
      destruct cl2 as [[cl'A cl'T] [cl'eq cl'in]].
      inversion cl'eq. subst.
      cbn.
      lets* IH: H1 cl'in Alphas x Hlen Hdist.
      cbn in IH.
      instantiate (1:=(L \u \{ Z })) in Afresh.
      rewrite* <- subst_commutes_with_unrelated_opens_te_ee.
      * rewrite* subst_ee_open_ee_var.
        apply* IH.
        intros A AAlpha.
        assert (A \notin L \u \{ Z }); solve [apply* Afresh | eauto].
      * intros A AAlpha.
        assert (A \notin L \u \{ Z }); solve [apply* Afresh | eauto].
  - induction 1; intros; simpl; auto;
      try match goal with
      | H: term (trm_abs _ _) |- _ => rename H into Hterm
      | H: term (trm_tabs _) |- _ => rename H into Hterm
      end.
    + apply value_abs. inversions Hterm.
      apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
    + apply value_tabs; inversions Hterm.
      apply_fresh* term_tabs as Y; rewrite* subst_ee_open_te_var.
    + econstructor.
      * econstructor.
        -- apply* value_is_term.
        -- inversion* H.
      * apply* IHvalue.
Qed.

Lemma rewrite_open_tt_many_gadt : forall OTs GTs N,
    open_tt_many OTs (typ_gadt GTs N) =
    typ_gadt (List.map (open_tt_many OTs) GTs) N.
  induction OTs as [| OTh OTt]; introv.
  - cbn. rewrite* List.map_id.
  - cbn.
    assert (List.map (fun T : typ => open_tt_many OTt (open_tt T OTh)) GTs = List.map (open_tt_many OTt) (List.map (open_tt_rec 0 OTh) GTs)).
    + rewrite List.map_map.
      apply* List.map_ext.
    + rewrite H.
      apply IHOTt.
Qed.


Fixpoint subst_tb_many (As : list var) (Us : list typ) (b : bind) : bind :=
  match (As, Us) with
  | (List.cons Ah At, List.cons Uh Ut) => subst_tb_many At Ut (subst_tb Ah Uh b)
  | _ => b
  end.

Lemma adding_free_is_ok : forall A E F,
    ok (E & F) ->
    A # E ->
    A # F ->
    ok (E & (withtyp A) & F)%env.
  induction F using env_ind; introv Hok HE HF.
  - rewrite concat_empty_r.
    constructor*.
  - rewrite concat_assoc.
    rewrite concat_assoc in Hok.
    apply ok_push_inv in Hok.
    econstructor.
    + apply* IHF.
    + simpl_dom.
      rewrite notin_union.
      rewrite notin_union.
      split*.
Qed.

Lemma adding_free_is_ok_many : forall As E F,
    ok (E & F) ->
    DistinctList As ->
    (forall A, List.In A As -> A \notin dom E) ->
    (forall A, List.In A As -> A \notin dom F) ->
    ok (add_types E As & F).
  induction As as [| Ah Ats]; introv Hok HD HE HF.
  - cbn. eauto.
  - cbn.
    rewrite <- concat_assoc.
    apply IHAts; eauto with listin.
    + rewrite concat_assoc.
      apply adding_free_is_ok; eauto with listin.
    + inversion* HD.
    + introv Hin.
      simpl_dom.
      rewrite notin_union.
      split.
      * apply* notin_singleton.
        inversions HD.
        intro; subst. contradiction.
      * eauto with listin.
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

Lemma notin_fv_tt_open : forall Y X T,
    X \notin fv_typ (T open_tt_var Y) ->
    X \notin fv_typ T.
Proof.
  unfold open_tt.
  introv FO.
  lets* characterized: fv_open T (typ_fvar Y) 0.
  destruct characterized as [Hc | Hc]; rewrite Hc in FO; eauto.
Qed.

Lemma binds_ext : forall A (x : var) (v1 v2 : A) E,
    binds x v1 E ->
    binds x v2 E ->
    v1 = v2.
  induction E using env_ind; introv b1 b2.
  - exfalso. apply* binds_empty_inv.
  - lets* [[? ?] | [? ?]]: binds_push_inv b1;
      lets* [[? ?] | [? ?]]: binds_push_inv b2.
      subst; trivial.
Qed.

Lemma subst_idempotent : forall U Z P,
    Z \notin fv_typ P ->
    subst_tt Z P U = subst_tt Z P (subst_tt Z P U).
  induction U using typ_ind'; introv FV; try solve [cbn; eauto].
  - cbn.
    case_if.
    + rewrite* subst_tt_fresh.
    + cbn. case_if. eauto.
  - cbn.
    rewrite* <- IHU1.
    rewrite* <- IHU2.
  - cbn.
    rewrite* <- IHU1.
    rewrite* <- IHU2.
  - cbn.
    rewrite* <- IHU.
  - cbn. f_equal.
    rewrite List.map_map.
    apply* List.map_ext_in.
    introv ain.
    rewrite List.Forall_forall in *.
    eauto.
Qed.

Lemma subst_idempotent_through_many_open : forall Tts Z U P,
    type P ->
    Z \notin fv_typ P ->
    subst_tt Z P (open_tt_many Tts U) =
    subst_tt Z P (open_tt_many Tts (subst_tt Z P U)).
  induction Tts; introv TP FV.
  - cbn. apply* subst_idempotent.
  - cbn.
    rewrite* IHTts.
    rewrite* (IHTts Z (open_tt (subst_tt Z P U) a) P).
    f_equal. f_equal.
    repeat rewrite* subst_tt_open_tt.
    f_equal.
    apply* subst_idempotent.
Qed.

Lemma list_fold_map : forall (A B : Type) (ls : list A) (f : B -> A -> B) (g : A -> A) (z : B),
    List.fold_left (fun a b => f a b) (List.map g ls) z
    =
    List.fold_left (fun a b => f a (g b)) ls z.
  induction ls; introv; cbn; eauto.
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

Lemma subst_removes_var : forall T U Z,
    Z \notin fv_typ U ->
    Z \notin fv_typ (subst_tt Z U T).
  induction T using typ_ind'; introv FU; cbn; eauto.
  - case_if; cbn; eauto.
  - rewrite list_fold_map.
    rewrite List.Forall_forall in *.
    apply* notin_fold.
Qed.

Lemma subst_commutes_open_tt_many : forall Ts Z P U,
    type P ->
    Z \notin fv_typ P ->
    Z \notin fv_typ U ->
    subst_tt Z P (open_tt_many Ts U) =
    open_tt_many (List.map (subst_tt Z P) Ts) U.
  induction Ts as [| Th Tts]; introv TP FP FU.
  - cbn. apply* subst_tt_fresh.
  - cbn.
    rewrite* subst_idempotent_through_many_open.
    rewrite* subst_tt_open_tt.
    rewrite* (@subst_tt_fresh Z P U).
    apply* IHTts.
    unfold open_tt.
    lets* FO: fv_open U (subst_tt Z P Th) 0.
    destruct FO as [FO | FO].
    + rewrite FO.
      apply notin_union; split*.
      apply* subst_removes_var.
    + rewrite* FO.
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
