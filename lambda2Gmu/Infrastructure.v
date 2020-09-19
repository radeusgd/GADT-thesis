Set Implicit Arguments.
Require Import Definitions.
Require Import TLC.LibLN.
Require Import Psatz.
Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Wf_nat.
(* large portions of this are based on the TLC formalisation of FSub *)
Hint Constructors type term wft typing red value.

Hint Resolve typing_var typing_app typing_tapp.

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
  constr:(A \u B \u C \u E \u F).

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


(* Lemma open_tt_rec_type_core : forall T j V U i, i <> j -> *)
(*   (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) -> *)
(*   T = open_tt_rec i U T. *)
(* Proof. *)
(*   induction T using typ_ind' ; introv Neq Heq; simpl in *; inversion Heq; f_equal*. *)
(*   - crush_compare; crush_compare. *)
(*     + intuition. *)
(*     + subst. admit. *)
(*     + subst. admit. *)
(*     + admit. *)
(*   - apply map_id. *)
(*     introv Lin. *)
(*     handleforall. *)
(*     eapply Hforall. *)
(*     + auto. *)
(*     + exact Neq. *)
(*     + rewritemapmap. *)
(*       eapply ext_in_map in Hmapmap. exact Hmapmap. *)
(*       auto. *)
(* Admitted. *)

Fixpoint open_bvar_level_count_typ (T : typ) : nat :=
  match T with
  | typ_bvar J => J + 1
  | typ_fvar X => 0
  | typ_unit   => 0
  | T1 ** T2   => max (open_bvar_level_count_typ T1) (open_bvar_level_count_typ T2)
  | T1 ==> T2   => max (open_bvar_level_count_typ T1) (open_bvar_level_count_typ T2)
  | typ_all T1 => (open_bvar_level_count_typ T1) - 1
  | typ_gadt Ts _ => fold_left (fun acc T => max acc (open_bvar_level_count_typ T)) Ts 0
  end.

Lemma fold_open_tt : forall T X,
    open_tt_rec 0 (typ_fvar X) T = T open_tt_var X.
  eauto.
Qed.

Lemma max_zero : forall a b,
    max a b = 0 ->
    a = 0 /\ b = 0.
  introv Hmax; split; try lia.
Qed.

Lemma max_lesser : forall a b k,
    k >= max a b ->
    k >= a /\ k >= b.
  intros; try lia.
Qed.

(*
  T : typ
  IHT : forall X : var,
        open_bvar_level_count_typ (T open_tt_var X) = 0 ->
        open_bvar_level_count_typ T <= 1
  X : var
  Hopen : open_bvar_level_count_typ (open_tt_rec 1 (typ_fvar X) T) - 1 = 0
  ============================
  open_bvar_level_count_typ T - 1 <= 1
 *)

Require Import TLC.LibLogic.

(* (* Lemma opening_decrease_core : forall T X k, *) *)
(* (*     open_bvar_level_count_typ (open_tt_rec k (typ_fvar X) T) >= open_bvar_level_count_typ T - 1. *) *)
(* (*   induction T using typ_ind'; introv. *) *)
(* (*   - unfolds open_tt; unfolds open_tt_rec. *) *)
(* (*     crush_compare; subst; cbn. *) *)
(* (*     +  *) *)
(* (*   - cbn; eauto. *) *)
(* (*   - cbn; eauto. *) *)
(* (*   - lets* IH1: IHT1 X. *) *)
(* (*     lets* IH2: IHT2 X. *) *)
(* (*     cbn. unfolds open_tt. lia. *) *)
(* (*   - lets* IH1: IHT1 X. *) *)
(* (*     lets* IH2: IHT2 X. *) *)
(* (*     cbn. unfolds open_tt. lia. *) *)
(* (*   - cbn. *) *)
(* (*     lets* IH: IHT X. *) *)
(* (*   Abort. *) *)

(* Lemma opening_decrease : forall T X, *)
(*     open_bvar_level_count_typ (T open_tt_var X) >= open_bvar_level_count_typ T - 1. *)
(*   induction T using typ_ind'; introv. *)
(*   - unfolds open_tt; unfolds open_tt_rec; *)
(*       crush_compare; subst; cbn; lia. *)
(*   - cbn; eauto. *)
(*   - cbn; eauto. *)
(*   - lets* IH1: IHT1 X. *)
(*     lets* IH2: IHT2 X. *)
(*     cbn. unfolds open_tt. lia. *)
(*   - lets* IH1: IHT1 X. *)
(*     lets* IH2: IHT2 X. *)
(*     cbn. unfolds open_tt. lia. *)
(*   - cbn. *)
(*     lets* IH: IHT X. *)
(* Admitted. *)


(* Lemma contraposed_closed_bvar_level : forall T, *)
(*     open_bvar_level_count_typ T > 0 -> not(type T). *)
(*   introv Hopen. *)
(*   intro Htype. *)
(*   induction Htype; try (cbn in Hopen; lia). *)
(*   - pick_fresh X. *)
(*     assert (Htyp: type (T2 open_tt_var X)); eauto. *)
(*     assert (Hcount: open_bvar_level_count_typ (T2 open_tt_var X) > 0 -> False); eauto. *)
(*     + apply* H0. *)
(*     + apply Hcount. *)
(*       cbn in Hopen. *)

(*       assert (open_bvar_level_count_typ (T2 open_tt_var X) >= open_bvar_level_count_typ T2 - 1). *)
(*       * admit. *)
(*       * lia. *)
(*   - cbn in Hopen. *)
(*     (* ughh complicated arighmetic proof *) *)
(*     admit. *)
(* Admitted. *)

(* Lemma closed_bvar_level : forall T, *)
(*     type T -> open_bvar_level_count_typ T = 0. *)
(*   intro T. *)
(*   apply contrapose_inv. *)
(*   intro Hneq. *)
(*   apply contraposed_closed_bvar_level. *)
(*   lia. *)
(* Qed. *)

(* Lemma closed_after_level : forall T k U, *)
(*     k >= open_bvar_level_count_typ T -> *)
(*     T = open_tt_rec k U T. *)
(*   induction T using typ_ind'; introv Hk; eauto. *)
(*   - cbn in Hk. *)
(*     assert (Hkk: k > n); try lia. *)
(*     cbn. crush_compare. *)
(*   - cbn in Hk. *)
(*     apply max_lesser in Hk. *)
(*     destruct Hk as [Hk1 Hk2]. *)
(*     cbn. *)
(*     eapply IHT1 in Hk1. *)
(*     eapply IHT2 in Hk2. *)
(*     erewrite <- Hk1. *)
(*     erewrite <- Hk2. *)
(*     trivial. *)
(*   - cbn in Hk. *)
(*     apply max_lesser in Hk. *)
(*     destruct Hk as [Hk1 Hk2]. *)
(*     cbn. *)
(*     eapply IHT1 in Hk1. *)
(*     eapply IHT2 in Hk2. *)
(*     erewrite <- Hk1. *)
(*     erewrite <- Hk2. *)
(*     trivial. *)
(*   - cbn in Hk. *)
(*     cbn. *)
(*     lets* IH: IHT (S k) U. *)
(*     assert (S k >= open_bvar_level_count_typ T); try lia. *)
(*     apply IH in H. rewrite <- H. trivial. *)
(*   - admit. *)
(* Admitted. *)

Print Forall.
Fixpoint closed_in_surroundings (k : nat) (T : typ) {struct T} : Prop :=
  match T with
  | typ_bvar J => J < k
  | typ_fvar X => True
  | typ_unit   => True
  | T1 ** T2   => closed_in_surroundings k T1 /\ closed_in_surroundings k T2
  | T1 ==> T2   => closed_in_surroundings k T1 /\ closed_in_surroundings k T2
  | typ_all T1 => closed_in_surroundings (S k) T1
  | typ_gadt Ts _ => fold_left (fun acc T => acc /\ closed_in_surroundings k T) Ts True
  end.

Lemma fold_or_is_forall : forall A Ts (P : A -> Prop),
    fold_left (fun acc T => acc /\ P T) Ts True ->
    Forall P Ts.
  intros.
  induction Ts; eauto.
Admitted.

Lemma closed_id : forall T U n k,
    closed_in_surroundings n T ->
    k >= n ->
    T = open_tt_rec k U T.
Admitted.

Lemma type_closed : forall T,
    type T -> closed_in_surroundings 0 T.
Admitted.

(* TODO continue from here *)

Lemma open_tt_rec_type : forall T U,
  type T -> forall k, T = open_tt_rec k U T.
Proof.
  introv Htype.
  lets* Hlevel: closed_bvar_level T.
  apply Hlevel in Htype.
  intros.
  apply closed_after_level.
  rewrite Htype.
  lia.
Qed.


  (* induction T using strong_induction_on_typ_size; *)
  (*   intros; subst. *)
  (* Ltac inv_typ := match goal with | H: type ?T |- _ => inversions H end. *)
  (* destruct T; try solve [ *)
  (*                   inv_typ *)
  (*                 | cbv; auto *)
  (*                 ]. *)
  (* - inv_typ. *)
  (*   cbn. *)
  (*   lets* IH1: H T1 U k; try (cbn; lia). *)
  (*   lets* IH2: H T2 U k; try (cbn; lia). *)
  (*   rewrite <- IH1. *)
  (*   rewrite <- IH2. *)
  (*   trivial. *)
  (* - inv_typ. *)
  (*   cbn. *)
  (*   lets* IH1: H T1 U k; try (cbn; lia). *)
  (*   lets* IH2: H T2 U k; try (cbn; lia). *)
  (*   rewrite <- IH1. *)
  (*   rewrite <- IH2. *)
  (*   trivial. *)
  (* - inv_typ. *)
  (*   cbn. *)
  (*   pick_fresh X. *)
  (*   assert (Htype: type (T open_tt_var X)); eauto. *)
  (*   lets* IH: H (T open_tt_var X) U (k). *)
  (*   + cbn. *)
  (*     lets* Hsize: open_tt_var_preserves_size T X 0. *)
  (*     unfolds open_tt. *)
  (*     rewrite <- Hsize. *)
  (*     lia. *)
  (*   + admit. *)
  (* - inv_typ. *)
  (*   cbn. *)
  (*   admit. *)
  (* (* induction 1; intros; simpl; f_equal*. *) *)
  (* (* - unfolds open_tt. *) *)
  (* (*   pick_fresh X. (* apply* (@open_tt_rec_type_core T2 0 (typ_fvar X)). *) *) *)
  (* (*   admit. *) *)
  (* (* - apply map_id. *) *)
  (* (*   auto. *) *)
(* Admitted. *)

(** Substitution for a fresh name is identity. *)


  (* H0 : Z \notin List.fold_left (fun (fv : fset var) (T : typ) => fv \u fv_typ T) ls \{} *)
  (* x : typ *)
  (* Lin : List.In x ls *)
  (* ============================ *)
  (* Z \notin fv_typ x *)

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


(* ********************************************************************** *)
(** ** Properties of type substitution in terms *)

Lemma open_te_rec_term_core : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros; simpl in *; inversion H; f_equal*; f_equal*.
Qed.


(* TODO same as above *)
(* Lemma open_typlist_rec_type_core : forall l j Q i P, *)
(*     open_typlist_rec j Q l = open_typlist_rec i P (open_typlist_rec j Q l) -> *)
(*     i <> j -> *)
(*     l = open_typlist_rec i P l. *)
(*   induction l; intros; simpl in *; inversion H; f_equal*; *)
(*     try match goal with H: ?i <> ?j |- ?t = open_tt_rec ?i _ ?t => *)
(*                         apply* (@open_tt_rec_type_core t j) end. *)
(* Qed. *)

Lemma open_te_rec_type_core : forall e j Q i P, i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros; simpl in *; inversion H0; f_equal*;
    try match goal with H: ?i <> ?j |- ?t = open_tt_rec ?i _ ?t =>
                        apply* (@open_tt_rec_type_core t j) end.
  (* - apply* open_typlist_rec_type_core. *)
Admitted.

Lemma open_te_rec_term : forall e U,
  term e -> forall k, e = open_te_rec k U e.
Proof.
  (* intros e U WF. induction WF; intro k; simpl; *)
  (*                  f_equal*; try solve [ apply* open_tt_rec_type ]. *)
  (* - destruct k. *)
  (*   + eapply open_typlist_rec_type_core. *)
  (*     2: { *)
  (*       auto. *)
  (*     } *)
  (*     unfold open_typlist_rec. *)
  (*     rewrite List.map_map. *)
  (*     apply List.map_ext_in. *)
  (*     introv Tin. *)
  (*     apply open_tt_rec_type. *)
  (*     instantiate (1:=U). *)
  (*     rewrite* <- open_tt_rec_type. *)
  (*   + eapply open_typlist_rec_type_core. *)
  (*     2: { *)
  (*       instantiate (1:=0). auto. *)
  (*     } *)
  (*     unfold open_typlist_rec. *)
  (*     rewrite List.map_map. *)
  (*     apply List.map_ext_in. *)
  (*     introv Tin. *)
  (*     apply open_tt_rec_type. *)
  (*     instantiate (1:=U). *)
  (*     rewrite* <- open_tt_rec_type. *)
  (* - unfolds open_ee. pick_fresh x. *)
  (*   apply* (@open_te_rec_term_core e1 0 (trm_fvar x)). *)
  (* - unfolds open_te. pick_fresh X. *)
  (*   apply* (@open_te_rec_type_core e1 0 (typ_fvar X)). *)
  (* - unfolds open_ee. pick_fresh x. *)
  (*   apply* (@open_te_rec_term_core v1 0 (trm_fvar x)). *)
  (* - unfolds open_ee. pick_fresh x. *)
  (*   apply* (@open_te_rec_term_core e2 0 (trm_fvar x)). *)
Admitted.

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
  - destruct IHtyping as [Hokt [Hterm Hwft]].
    subst.
    splits*.
    + constructor*.
      introv Tin.
      unfold open_tt_many in *.
      admit.
    + assert (okGadt Σ) as Hgadt.
      * apply* okt_implies_okgadt.
      * admit.
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
  - subst. splits*. destruct IHtyping as [? [? Hwft]]. inversions Hwft.
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

