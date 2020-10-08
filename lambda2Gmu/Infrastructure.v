Set Implicit Arguments.
Require Import Definitions.
Require Import TLC.LibLN.
Require Import TLC.LibEnv.
Require Import TLC.LibLogic.
Require Import Psatz.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Wf_nat.
Require List.
(* large portions of this are based on the TLC formalisation of FSub *)
Hint Constructors type term wft typing red value.

Hint Resolve typing_var typing_app typing_tapp.

Ltac listin :=
  match goal with
  | |- List.In ?e (?h :: ?t) =>
    cbn; solve [right* | left*]
  end.

Hint Extern 4 (List.In _ (_ :: _)) => (cbn; solve [left* | right*]) : listin.

Lemma value_is_term : forall e, value e -> term e.
  induction e; intro Hv; inversion Hv; eauto.
Qed.

(** Gathering free names already used in the proofs *)
Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv_trm x) in
  let E := gather_vars_with (fun x : typ => fv_typ x) in
  let F := gather_vars_with (fun x : ctx => dom x) in
  let G := gather_vars_with (fun x : list var => from_list x) in
  constr:(A \u B \u C \u E \u F \u G).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.

Ltac get_env :=
  match goal with
  | |- wft ?E _ => E
  | |- typing ?E _ _ => E
  end.

Ltac handleforall :=
  let Hforall := fresh "Hforall" in
  match goal with
  | H: List.Forall ?P ?ls |- _ => rename H into Hforall; rewrite List.Forall_forall in Hforall
  end.

Ltac rewritemapmap :=
  let H' := fresh "Hmapmap" in
  match goal with
  | H: List.map ?f ?ls = (List.map ?g (List.map ?h ?ls)) |- _ => rename H into H'; rewrite List.map_map in H'
  end.

Ltac decide_compare i j :=
  let CMP := fresh "CMP" in
  let EQ := fresh "EQ" in
  remember (i ?= j) as CMP eqn: EQ;
  symmetry in EQ;
  destruct CMP;
  match goal with
  | H: (i ?= j) = Eq |- _ => apply nat_compare_eq in H
  | H: (i ?= j) = Lt |- _ => apply nat_compare_lt in H
  | H: (i ?= j) = Gt |- _ => apply nat_compare_gt in H
  end.

Ltac crush_compare :=
  match goal with
  | H: context [(?i ?= ?j)] |- _ => decide_compare i j; (try lia); eauto
  | |- context [(?i ?= ?j)] => decide_compare i j; (try lia); eauto
  end.

Lemma test_compare : forall i j, i <> j -> (match compare i j with | Lt => 0 | Gt => 0 | Eq => 1 end) = 0.
  intros.
  crush_compare.
Qed.

Ltac decide_eq i j :=
  let CMP := fresh "CMP" in
  let EQ := fresh "EQ" in
  remember (i =? j) as CMP eqn: EQ;
  symmetry in EQ;
  destruct CMP;
  match goal with
  | H: (i =? j) = true |- _ => apply beq_nat_true in H
  | H: (i =? j) = false |- _ => apply beq_nat_false in H
  end.

Ltac crush_eq :=
  match goal with
  | H: context [(?i =? ?j)] |- _ => decide_eq i j; eauto
  | |- context [(?i =? ?j)] => decide_eq i j; eauto
  end.

Lemma test_eq : forall i j, i <> j -> (if i =? j then 1 else 0) = 0.
  intros.
  crush_eq.
  intuition.
Qed.

(* Based on: https://github.com/tchajed/strong-induction/blob/master/StrongInduction.v *)
Lemma strong_induction (P : nat -> Prop): (forall m, (forall k, k < m -> P k) -> P m) -> forall n, P n.
  apply Wf_nat.induction_ltof1.
Qed.

Lemma strong_induction_on_term_size_helper : forall (P : trm -> Prop),
    (forall n, (forall e, trm_size e < n -> P e) -> forall e, trm_size e = n -> P e) ->
    forall n e, trm_size e = n -> P e.
  introv IH.
  lets K: strong_induction (fun n => forall e, trm_size e = n -> P e).
  apply K.
  introv IHk.
  lets IHm: IH m.
  apply IHm.
  intros.
  eapply IHk; eauto.
Qed.

Lemma strong_induction_on_term_size : forall (P : trm -> Prop),
    (forall n, (forall e, trm_size e < n -> P e) -> forall e, trm_size e = n -> P e) ->
    forall e, P e.
  intros.
  pose (n := trm_size e).
  eapply strong_induction_on_term_size_helper; eauto.
Qed.

(* TODO DRY *)
Lemma strong_induction_on_type_size_helper : forall (P : typ -> Prop),
    (forall n, (forall e, typ_size e < n -> P e) -> forall e, typ_size e = n -> P e) ->
    forall n e, typ_size e = n -> P e.
  introv IH.
  lets K: strong_induction (fun n => forall e, typ_size e = n -> P e).
  apply K.
  introv IHk.
  lets IHm: IH m.
  apply IHm.
  intros.
  eapply IHk; eauto.
Qed.

Lemma strong_induction_on_typ_size : forall (P : typ -> Prop),
    (forall n, (forall T, typ_size T < n -> P T) -> forall T, typ_size T = n -> P T) ->
    forall T, P T.
  intros.
  pose (n := typ_size T).
  eapply strong_induction_on_type_size_helper; eauto.
Qed.


Lemma open_ee_var_preserves_size : forall e x n,
    trm_size e = trm_size (open_ee_rec n (trm_fvar x) e).
  induction e; introv; try solve [cbn; try case_if; cbn; eauto].
Qed.
Lemma open_te_var_preserves_size : forall e x n,
    trm_size e = trm_size (open_te_rec n (typ_fvar x) e).
  induction e; introv; try solve [cbn; try case_if; cbn; eauto].
Qed.


Lemma open_tt_var_preserves_size : forall T X n,
    typ_size T = typ_size (open_tt_rec n (typ_fvar X) T).
  induction T using typ_ind' ; introv; try solve [cbn; try case_if; cbn; eauto].
  - cbn. crush_compare.
  - cbn.
    rewrite List.map_map.
    assert ((List.map typ_size ls) = (List.map (fun x : typ => typ_size (open_tt_rec n0 (typ_fvar X) x)) ls)) as Hmapeq.
    + apply List.map_ext_in.
      rewrite <- list_quantification in H.
      intros. apply* H.
    + rewrite Hmapeq. auto.
Qed.

(* (** These tactics help applying a lemma which conclusion mentions *)
(*   an environment (E & F) in the particular case when F is empty *) *)
(* Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) := *)
(*   let E := get_env in rewrite <- (concat_empty E); *)
(*   eapply lemma; try rewrite concat_empty. *)

(* Tactic Notation "apply_empty" constr(F) := *)
(*   apply_empty_bis (get_env) F. *)

(* Tactic Notation "apply_empty" "*" constr(F) := *)
(*   apply_empty F; auto*. *)

Ltac unsimpl_map_bind :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U) ] =>
    unsimpl ((subst_tb Z P) (B U)) end.

Tactic Notation "unsimpl_map_bind" "*" :=
  unsimpl_map_bind; auto_star.

Lemma map_id : forall (A : Type) (f : A -> A) (ls : list A),
    (forall x, List.In x ls -> x = f x) ->
    ls = List.map f ls.
  introv feq.
  induction ls.
  - auto.
  - cbn.
    rewrite <- feq.
    + rewrite <- IHls.
      * auto.
      * intros.
        apply feq.
        apply* List.in_cons.
    + constructor*.
Qed.

(* adapted from a newer version of Coq stdlib:
https://github.com/coq/coq/blob/master/theories/Lists/List.v
*)
Lemma ext_in_map :
  forall (A B : Type)(f g:A->B) l, List.map f l = List.map g l -> forall a, List.In a l -> f a = g a.
Proof. induction l; intros [=] ? []; subst; auto. Qed.

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

Ltac crush_open :=
  (try unfold open_tt); (try unfold open_tt_rec); crush_compare.

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

Lemma fv_fold_base : forall x ls base,
    x \notin List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) ls base ->
    x \notin base.
  induction ls.
  - introv Hfold. cbn in Hfold. auto.
  - introv Hfold. cbn in Hfold.
    assert (x \notin base \u fv_typ a).
    + apply* IHls.
    + auto.
Qed.

Lemma fv_fold : forall Z x ls base,
    Z \notin List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) ls base ->
    List.In x ls ->
    Z \notin fv_typ x.
  induction ls; introv ZIL Lin.
  - false*.
  - apply List.in_inv in Lin.
    destruct Lin.
    + cbn in ZIL.
      apply fv_fold_base in ZIL. subst. auto.
    + apply* IHls.
Qed.

Hint Resolve fv_fold_base fv_fold.

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

Hint Immediate subset_refl subset_empty_l subset_union_weak_l subset_union_weak_r subset_union_2 union_comm union_assoc union_same.

Lemma subset_union_3 : forall T (A B C : fset T),
    (A \u B) \u C = (A \u C) \u (B \u C).
  intros.
  assert (CuC: C \u C = C); try apply union_same.
  rewrite <- CuC at 1.
  rewrite <- union_assoc.
  rewrite union_comm.
  rewrite union_assoc.
  rewrite <- union_assoc.
  rewrite union_comm.
  assert (CuA: C \u A = A \u C); try apply union_comm.
  rewrite* CuA.
Qed.


Lemma fold_map : forall A B bs G F a0,
    List.fold_left (fun (a : A) (b : B) => G a b) (List.map F bs) a0 =
    List.fold_left (fun (a : A) (b : B) => G a (F b)) bs a0.
  induction bs; intros.
  - cbn. eauto.
  - cbn.
    apply* IHbs.
Qed.

Lemma union_fold_detach : forall B (ls : list B) (P : B -> fset var) (z : fset var) (z' : fset var),
    List.fold_left (fun (a : fset var) (b : B) => a \u P b) ls (z \u z')
    =
    List.fold_left (fun (a : fset var) (b : B) => a \u P b) ls z \u z'.
  induction ls; introv.
  - cbn. eauto.
  - cbn.
    assert (Horder: ((z \u z') \u P a) = ((z \u P a) \u z')).
    + rewrite union_comm.
      rewrite union_assoc.
      rewrite (union_comm (P a) z).
      eauto.
    + rewrite Horder.
      apply* IHls.
Qed.

Lemma fv_smaller : forall T U k,
    fv_typ (open_tt_rec k U T) \c (fv_typ T \u fv_typ U).
  induction T using typ_ind'; introv;
    try solve [
          unfold open_tt_rec; crush_compare
        | cbn; eauto
        | cbn; fold (open_tt T1 U); fold (open_tt T2 U);
          rewrite subset_union_3;
          apply* subset_union_2
        ].
  cbn.
  rewrite List.Forall_forall in *.
  rewrite fold_map.
  induction ls.
  - cbn. eauto.
  - cbn.
    rewrite union_fold_detach.
    rewrite union_fold_detach.
    rewrite subset_union_3.
    apply subset_union_2.
    + apply* IHls.
      introv xils.
      apply* H. cbn; right*.
    + apply* H. constructor*.
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
  induction e; intros; simpl in *; inversion H; f_equal*; f_equal*.
Qed.


(* Lemma open_typlist_rec_type_core : forall l j Q i P, *)
(*     open_typlist_rec j Q l = open_typlist_rec i P (open_typlist_rec j Q l) -> *)
(*     i <> j -> *)
(*     l = open_typlist_rec i P l. *)
(*   induction l; intros; simpl in *; inversion H; f_equal*; *)
(*     try match goal with H: ?i <> ?j |- ?t = open_tt_rec ?i _ ?t => *)
(*                         apply* (@open_tt_rec_type_core t j) end. *)
(* Admitted. *)

(* Lemma open_te_rec_type_core : forall e j Q i P, i <> j -> *)
(*   open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) -> *)
(*   e = open_te_rec i P e. *)
(* Proof. *)
(*   induction e; intros; simpl in *; inversion H0; f_equal*; *)
(*     try match goal with H: ?i <> ?j |- ?t = open_tt_rec ?i _ ?t => *)
(*                         apply* (@open_tt_rec_type_core t j) end. *)
(*   - admit. *)
(*     (* apply* open_typlist_rec_type_core. *) *)
(* Admitted. *)

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
    te_closed_in_surroundings k (trm_constructor Ts N e).

Lemma te_opening_te_adds_one : forall e X k n,
    te_closed_in_surroundings n (open_te_rec k (typ_fvar X) e) ->
    te_closed_in_surroundings (max (S n) (S k)) e.
  induction e; introv Hc; inversions Hc;
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
Qed.

Lemma te_opening_ee_preserves : forall e x k n,
    te_closed_in_surroundings n (open_ee_rec k (trm_fvar x) e) ->
    te_closed_in_surroundings n e.
  induction e; introv Hc; try solve [inversions Hc; constructor*].
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
  -  constructor*. apply* type_closed.
Qed.

Lemma te_closed_id : forall e T n k,
    te_closed_in_surroundings n e ->
    k >= n ->
    e = open_te_rec k T e.
  induction e; introv Hc Hk; eauto; inversions Hc; cbn; f_equal;
    try (match goal with
         | IH: forall T n k, ?P1 -> ?P2 -> ?e1 = open_te_rec k T ?e1 |- _ => apply* IH
         end);
    try apply* closed_id;
    try lia.
  unfold open_typlist_rec.
  rewrite <- List.map_id at 1.
  apply* List.map_ext_in.
  intro U.
  rewrite List.Forall_forall in *.
  lets* HC: H2 U.
  lets*: closed_id U T n k.
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
  induction e; simpl; intros; f_equal*; autos* subst_tt_fresh.
  - symmetry.
    apply map_id. introv Lin.
    symmetry.
    apply* subst_tt_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_te_open_te : forall e T X U, type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T).
Proof.
  intros. unfold open_te. generalize 0.
  induction e; intro n0; simpls; f_equal*;
    autos* subst_tt_open_tt_rec.
  - unfold open_typlist_rec.
    rewrite List.map_map.
    rewrite List.map_map.
    apply List.map_ext.
    intro.
    apply* H0.
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
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  crush_eq. crush_eq. subst. intuition.
Qed.

Lemma open_ee_rec_type_core : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv H; simpls; inversion H; f_equal*.
Qed.

Lemma open_ee_rec_term : forall u e,
  term e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intro k; simpl; f_equal*.
  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).

  - unfolds open_te.
    pick_fresh X.
    apply* (@open_ee_rec_type_core e1 0 (typ_fvar X)).

  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core v1 0 (trm_fvar x)).

  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e2 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)
Lemma subst_ee_fresh : forall x u e,
  x \notin fv_trm e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  - case_var*.
Qed.

(** Substitution distributes on the open operation. *)
Lemma subst_ee_open_ee : forall t1 t2 u x, term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intro n0; simpls; f_equal*.
  - crush_eq.
  - case_var*. rewrite* <- open_ee_rec_term.
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
  induction e; intros; simpl; f_equal*. crush_eq.
Qed.

(** Interactions between term substitutions in terms and opening
  with type variables in terms. *)

Lemma subst_ee_open_te_var : forall z u e X, term u ->
  (subst_ee z u e) open_te_var X = subst_ee z u (e open_te_var X).
Proof.
  introv. unfold open_te. generalize 0.
  induction e; intros; simpl; f_equal*.
  case_var*. symmetry. autos* open_te_rec_term.
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

Hint Resolve subst_tt_type subst_te_term subst_ee_term.
Hint Resolve subst_te_value subst_ee_value.

(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma type_from_wft : forall Σ E T,
  wft Σ E T -> type T.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve type_from_wft.

Lemma values_decidable : forall t,
    term t ->
    (value t \/ ~ (value t)).
  induction t; intro H;
  inversion H; subst; try solve [
                     right; intro Hv; inversion Hv
                   | left; econstructor
                          ].
  - match goal with
    | H: term t |- _ => rename H into Ht end.
    apply IHt in Ht.
    destruct Ht as [Hv | Hv].
    + left; constructor*.
    + right. intro Hv'. inversion* Hv'.
  - match goal with
    | H: term t1 |- _ => rename H into Ht1 end.
    match goal with
    | H: term t2 |- _ => rename H into Ht2 end.
    apply IHt1 in Ht1.
    apply IHt2 in Ht2.
    destruct Ht1;
      destruct Ht2;
      try solve [ left; econstructor; eauto
                | right; intro Hv; inversion Hv; congruence ].
  - left; econstructor.
    econstructor; eauto.
  - left; econstructor.
    econstructor; eauto.
Qed.

Ltac IHap IH := eapply IH; eauto;
                try (unfold open_ee; rewrite <- open_ee_var_preserves_size);
                try (unfold open_te; rewrite <- open_te_var_preserves_size);
                cbn; lia.

Lemma wft_weaken : forall Σ E F G T,
    wft Σ (E & G) T ->
    ok (E & F & G) ->
    wft Σ (E & F & G) T.
  introv Hwft Hok. gen_eq K: (E & G). gen E F G.
  induction Hwft; intros; subst; auto.
  - (* case: var *)
    apply (@wft_var Σ (E0 & F & G) X).  apply* binds_weaken.
  - (* case: all *)
    apply_fresh* wft_all as X. apply_ih_bind* H0.
  - econstructor; eauto.
Qed.

Ltac expand_env_empty E :=
  let HE := fresh "HE" in
  assert (HE: E = E & empty); [
    rewrite* concat_empty_r
  | rewrite HE ].

Ltac fold_env_empty :=
  match goal with
  | |- context [?E & empty] =>
    let HE := fresh "HE" in
    assert (HE: E = E & empty); [
      rewrite* concat_empty_r
    | rewrite* <- HE ]
  end.

Ltac fold_env_empty_H :=
  match goal with
  | H: context [?E & empty] |- _ =>
    let HE := fresh "HE" in
    assert (HE: E = E & empty); [
      rewrite* concat_empty_r
    | rewrite* <- HE in H]
  | H: context [empty & ?E] |- _ =>
    let HE := fresh "HE" in
    assert (HE: E = empty & E); [
      rewrite* concat_empty_l
    | rewrite* <- HE in H]
  end.

Lemma okt_is_ok : forall Σ E, okt Σ E -> ok E.
  introv. intro Hokt.
  induction Hokt; eauto.
Qed.
Hint Extern 1 (ok _) => apply okt_is_ok.

Lemma wft_from_env_has_typ : forall Σ x U E,
    okt Σ E -> binds x (bind_var U) E -> wft Σ E U.
Proof.
  induction E using env_ind; intros Ok B.
  false* binds_empty_inv.
  inversions Ok.
  - false (empty_push_inv H).
  - destruct (eq_push_inv H) as [? [? ?]]; subst. clear H.
    destruct (binds_push_inv B) as [[? ?]|[? ?]]; subst.
    + inversions H1.
    + expand_env_empty (E & x0 ~ bind_typ); apply* wft_weaken; fold_env_empty.
      econstructor. apply* okt_is_ok. auto.
  - destruct (eq_push_inv H) as [? [? ?]]. clear H.
    destruct (binds_push_inv B) as [[? Hbindeq]|[? Hbinds]]; subst.
    + inversions Hbindeq.
      expand_env_empty (E & x0 ~ bind_var T); apply* wft_weaken; fold_env_empty.
      econstructor. apply* okt_is_ok. auto.
    + inversions Hbinds.
      expand_env_empty (E & x0 ~ bind_var T); apply* wft_weaken; fold_env_empty.
      constructor*.
      apply* okt_is_ok.
Qed.

(* TODO do some cleanup and move them around, probably separate files *)
Lemma wft_strengthen : forall Σ E F x U T,
 wft Σ (E & (x ~: U) & F) T -> wft Σ (E & F) T.
Proof.
  introv Hwft. gen_eq G: (E & (x ~: U) & F). gen F.
  induction Hwft; intros F EQ; subst; auto.
  -
    match goal with
    | H: binds _ _ _ |- _ =>
      rename H into Hbinds_bindtyp end.
    apply* (@wft_var).
    destruct (binds_concat_inv Hbinds_bindtyp) as [?|[? Hbinds2]].
    + apply~ binds_concat_right.
    + destruct (binds_push_inv Hbinds2) as [[? ?]|[? ?]].
      * subst. false.
      * apply~ binds_concat_left.
  - (* todo: binds_cases tactic *)
    match goal with
    | H: forall X, X \notin L -> forall F0, ?P1 -> ?P2 |- _ =>
      rename H into H_ctxEq_implies_wft end.
    apply_fresh* wft_all as Y. apply_ih_bind* H_ctxEq_implies_wft.
  - econstructor; eauto.
Qed.

Lemma okt_implies_okgadt : forall Σ E, okt Σ E -> okGadt Σ.
  induction 1; auto.
Qed.

Ltac find_ctxeq :=
  match goal with
  | H: _ & _ ~ _ = _ & _ ~ _ |- _ =>
    rename H into Hctx_eq
  end.

Lemma okt_push_var_inv : forall Σ E x T,
  okt Σ (E & x ~: T) -> okt Σ E /\ wft Σ E T /\ x # E.
Proof.
  introv O; inverts O.
  - false* empty_push_inv.
  - find_ctxeq. lets (?&?&?): (eq_push_inv Hctx_eq). false.
  - find_ctxeq. lets (?&M&?): (eq_push_inv Hctx_eq). subst. inverts~ M.
Qed.

Lemma okt_push_typ_inv : forall Σ E X,
  okt Σ (E & withtyp X) -> okt Σ E /\ X # E.
Proof.
  introv O. inverts O.
  - false* empty_push_inv.
  - find_ctxeq. lets (?&M&?): (eq_push_inv Hctx_eq). subst. inverts~ M.
  - find_ctxeq. lets (?&?&?): (eq_push_inv Hctx_eq). false.
Qed.

Lemma okt_push_inv : forall Σ E X B,
  okt Σ (E & X ~ B) -> B = bind_typ \/ exists T, B = bind_var T.
Proof.
  introv O; inverts O.
  - false* empty_push_inv.
  - lets (?&?&?): (eq_push_inv H). subst*.
  - lets (?&?&?): (eq_push_inv H). subst*.
Qed.

Lemma okt_strengthen : forall Σ E x U F,
    okt Σ (E & (x ~: U) & F) -> okt Σ (E & F).
  introv O. induction F using env_ind.
  - rewrite concat_empty_r in *. lets*: (okt_push_var_inv O).
  - rewrite concat_assoc in *.
    lets Hinv: okt_push_inv O; inversions Hinv.
    + lets (?&?): (okt_push_typ_inv O).
      applys~ okt_sub.
    + match goal with
      | H: exists T, v = bind_var T |- _ =>
        rename H into Hexists_bindvar end.
      inversions Hexists_bindvar.
      lets (?&?&?): (okt_push_var_inv O).
      applys~ okt_typ. applys* wft_strengthen.
Qed.


Ltac copy H :=
  let H' := fresh H in
  let Heq := fresh "EQ" in
  remember H as H' eqn:Heq; clear Heq.

Ltac copyTo H Hto :=
  let H' := fresh Hto in
  let Heq := fresh "EQ" in
  remember H as H' eqn:Heq; clear Heq.

Lemma okt_is_wft : forall Σ E x T,
    okt Σ (E & x ~: T) -> wft Σ E T.
  introv Hokt.
  inversion Hokt.
  - false* empty_push_inv.
  - lets (?&?&?): eq_push_inv H. false*.
  - lets (?&?&?): eq_push_inv H. subst.
    match goal with Heq: bind_var ?T1 = bind_var ?T2 |- _ => inversions* Heq end.
Qed.

Lemma okt_is_type : forall Σ E x T,
    okt Σ (E & x ~: T) -> type T.
  introv Hokt. apply okt_is_wft in Hokt. apply* type_from_wft.
Qed.

Ltac apply_folding E lemma :=
  expand_env_empty E; apply* lemma; fold_env_empty.

Ltac add_notin x L :=
  let Fr := fresh "Fr" in
  assert (Fr: x \notin L); auto.

Ltac unsimpl_map_bind_typ Z P :=
  match goal with
  | |- context [ bind_typ ] =>
    unsimpl (subst_tb Z P bind_typ)
  end.

Lemma wft_type : forall Σ E T,
    wft Σ E T -> type T.
Proof.
  induction 1; eauto.
Qed.

Lemma wft_subst_tb : forall Σ F E Z P T,
  wft Σ (E & (withtyp Z) & F) T ->
  wft Σ E P ->
  ok (E & map (subst_tb Z P) F) ->
  wft Σ (E & map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  introv WT WP. gen_eq G: (E & (withtyp Z) & F). gen F.
  induction WT as [ | | | | ? ? ? ? ? IH | ]; intros F EQ Ok; subst; simpl subst_tt; auto.
  - case_var*.
    + expand_env_empty (E & map (subst_tb Z P) F).
      apply* wft_weaken; fold_env_empty.
    + destruct (binds_concat_inv H) as [?|[? ?]].
      * apply wft_var.
        apply~ binds_concat_right.
        unsimpl_map_bind_typ Z P.
        apply~ binds_map.
      * destruct (binds_push_inv H1) as [[? ?]|[? ?]].
        -- subst. false~.
        -- applys wft_var. apply* binds_concat_left.
  - apply_fresh* wft_all as Y.
    unsimpl ((subst_tb Z P) bind_typ).
    lets: wft_type.
    rewrite* subst_tt_open_tt_var.
    apply_ih_map_bind* IH.
  - econstructor; eauto.
    + introv Tin.
      apply List.in_map_iff in Tin.
      destruct Tin as [T' Tand].
      destruct Tand as [Teq Tin].
      rewrite <- Teq.
      apply* H0.
    + apply List.map_length.
Qed.
Hint Resolve wft_subst_tb.

Lemma wft_open : forall Σ E U T1,
  ok E ->
  wft Σ E (typ_all T1) ->
  wft Σ E U ->
  wft Σ E (open_tt T1 U).
Proof.
  introv Ok WA WU. inversions WA. pick_fresh X.
  rewrite* (@subst_tt_intro X).
  lets K: (@wft_subst_tb Σ empty).
  specializes_vars K. clean_empty K. apply* K.
Qed.
Hint Resolve okt_is_ok.

Lemma aa : forall N M (X Y : typ) sig,
    sig = (N ~ X & M ~ Y) ->
    (forall m z, binds m z sig -> (z = X \/ z = Y)).
  intros; subst.
  apply binds_push_inv in H0.
  destruct H0.
  - intuition.
  - destruct H.
    apply binds_single_inv in H0.
    intuition.
Qed.

Lemma gadt_constructor_ok : forall Σ Name Tarity Ctors Ctor Carity CargType CretTypes,
    binds Name (GADT Tarity Ctors) Σ ->
    List.nth_error Ctors Ctor = Some (GADTconstr Carity CargType CretTypes) ->
    okGadt Σ ->
    okConstructorDef Σ Tarity (GADTconstr Carity CargType CretTypes).
  introv Hbind Hlist HokG.
  inversion HokG as [Hok HokG'].
  apply* HokG'.
  apply* List.nth_error_In.
Qed.

(* Lemma wft_open_gadt : forall , *)
(*   forall T : typ, List.In T Ts -> wft Σ E T *)
(*   Hokt : okt Σ E *)
(*   Hterm : term e1 *)
(*   Hwft : wft Σ E (open_tt_many CargType Ts) *)
(*   HG : okGadt Σ *)
(*        wft Σ (add_types empty Alphas) (open_tt_many_var retT Alphas) -> *)
(*   wft Σ E (open_tt_many (typ_gadt CretTypes Name) Ts) *)

Lemma rewrite_open_tt_many_gadt : forall OTs GTs N,
    open_tt_many OTs (typ_gadt GTs N) =
    typ_gadt (List.map (open_tt_many OTs) GTs) N.
Admitted.

Require Import TLC.LibFset TLC.LibList.
(* different Fset impl? taken from repo: *)
Lemma from_list_spec : forall A (x : A) L,
  x \in from_list L -> LibList.mem x L.
Proof using.
  unfold from_list. induction L; rew_listx.
  - rewrite in_empty. auto.
  - rewrite in_union, in_singleton.
    intro HH.
    destruct HH; eauto.
Qed.

Lemma from_list_spec2 : forall A (x : A) L,
    List.In x L -> x \in from_list L.
Proof using.
  unfold from_list. induction L; rew_listx.
  - rewrite in_empty. auto.
  - rewrite in_union, in_singleton.
    intro HH.
    destruct HH; eauto.
Qed.

Lemma exist_alphas : forall L len,
    exists (Alphas : list var),
      length Alphas = len /\ DistinctList Alphas /\ forall A, List.In A Alphas -> A \notin L.
  induction len.
  - exists (@List.nil var). splits*.
    + econstructor.
    + intuition.
  - inversion IHlen as [Alphas' [Hlen [Hdis Hnot]]].
    let x := gather_vars in idtac x.
    pick_fresh A.
    exists (List.cons A Alphas').
    splits*.
    + cbn. eauto.
    + constructor*.
      intro.
      assert (Hnot2: A \notin from_list Alphas'); eauto.
      apply Hnot2.
      apply* from_list_spec2.
    + introv AiA.
      inversions AiA; eauto.
Qed.

Lemma length_equality : forall A (a : list A),
    length a = Datatypes.length a.
  induction a; cbn; eauto.
Qed.

Lemma typing_regular : forall Σ E e T,
   {Σ, E} ⊢ e ∈ T -> okt Σ E /\ term e /\ wft Σ E T.
Proof.
  induction 1 as [ |
                   |
                   | ? ? ? ? ? ? ? IH
                   |
                   | ? ? ? ? ? ? ? IH
                   | | | |
                   | ? ? ? ? ? IHval ? IH
                   | ? ? ? ? ? ? ? ? ? ? IH
                   ];
    try solve [splits*].
  - splits*. apply* wft_from_env_has_typ.
  - subst. destruct IHtyping as [Hokt [Hterm Hwft]].
    subst.
    splits*.
    lets* HG: okt_implies_okgadt Hokt.
    lets* GADTC: gadt_constructor_ok HG.
    inversions GADTC.
    rewrite rewrite_open_tt_many_gadt.
    econstructor; eauto.
    + introv TiL.
      lets* TiL2: TiL. apply List.in_map_iff in TiL2.
      inversion TiL2 as [CretT [Heq CiC]]. subst.
      lets* EAlphas: exist_alphas (length Ts).
      inversion EAlphas as [Alphas [A1 [A2 A3]]].
      lets* HH: H10 Alphas CiC.
      * repeat rewrite <- length_equality.
        eauto.
      * admit.
    + rewrite List.map_length. trivial.
  - pick_fresh y.
    copyTo IH IH1.
    specializes IH y. destructs~ IH.
    forwards* Hctx: okt_push_inv.
    destruct Hctx as [? | Hctx]; try congruence.
    destruct Hctx as [U HU]. inversions HU.
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor. apply* okt_is_type.
      intros. apply* IH1.
    + econstructor.
      apply* okt_is_wft.
      apply_folding E wft_strengthen.
  - splits*.
    destruct IHtyping2 as [? [? Hwft]]. inversion* Hwft.
  - copyTo IH IH1.
    pick_fresh y. specializes IH y.
    add_notin y L. lets HF: IH Fr0. destructs~ HF.
    splits*.
    + forwards*: okt_push_typ_inv.
    + apply* term_tabs. intros. apply* IH1.
    + apply_fresh* wft_all as Y.
      add_notin Y L. lets HF: IH1 Y Fr1. destruct* HF.
  - subst. splits*. destruct IHtyping as [? [? Hwft]].
    copyTo Hwft Hwft2.
    inversions Hwft.
    match goal with
    | IH: forall X : var, X \notin L -> ?conclusion |- _ =>
      pick_fresh Y; add_notin Y L; lets HW: IH Y Fr0
    end.
    apply* wft_open.
  - splits*.
    destruct IHtyping as [? [? Hwft]]. inversion* Hwft.
  - splits*.
    destruct IHtyping as [? [? Hwft]]. inversion* Hwft.
  - pick_fresh y.
    copyTo IH IH1.
    specializes IH1 y. destructs~ IH1.
    forwards* Hp: okt_push_inv.
    destruct Hp as [? | Hex]; try congruence.
    destruct Hex as [U HU]. inversions HU.
    splits*.
    + apply_folding E okt_strengthen.
    + econstructor. apply* okt_is_type.
      intros. apply* IH.
      intros. apply* IHval.
    + apply_folding E wft_strengthen.
  - destructs IHtyping.
    pick_fresh y.
    copyTo IH IH1.
    specializes IH y. destructs~ IH.
    forwards* Hctx: okt_push_inv.
    destruct Hctx as [? | Hctx]; try congruence.
    destruct Hctx as [U HU]. inversions HU.
    splits*.
    + econstructor. auto.
      introv HxiL. lets HF: IH1 x HxiL. destruct* HF.
    + apply_folding E wft_strengthen.
Admitted.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; autos*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

(* Lemma red_regular : forall t t', *)
(*   red t t' -> term t /\ term t'. *)
(* Proof. *)
(*   induction 1; split; autos* value_regular. *)
(*   - inversions H. pick_fresh y. rewrite* (@subst_ee_intro y). *)
(*   - inversions H. pick_fresh Y. rewrite* (@subst_te_intro Y). *)
(*   - inversions H. pick_fresh y. rewrite* (@subst_ee_intro y). *)
(*   - inversions H. auto. *)
(*   - inversions H. auto. *)
(*   - inversions IHred. econstructor. *)
(* Qed. *)


Lemma typing_implies_term : forall Σ E e T,
    {Σ, E} ⊢ e ∈ T ->
    term e.
  intros.
  lets TR: typing_regular Σ E e T.
  destruct* TR.
Qed.

Lemma eq_dec_var (x y : var) : x = y \/ x <> y.
  lets: var_compare_eq x y.
  Require Import TLC.LibReflect.
  destruct (var_compare x y);
  rewrite isTrue_eq_if in H;
  case_if; auto.
Qed.

