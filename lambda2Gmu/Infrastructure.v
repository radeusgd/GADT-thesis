Require Import Definitions.
Require Import TLC.LibLN.
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

(** ** Properties of type substitution in type *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_tt_rec_type_core : forall T j V U i, i <> j ->
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof.
  induction T; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_tt_rec_type : forall T U,
  type T -> forall k, T = open_tt_rec k U T.
Proof.
  induction 1; intros; simpl; f_equal*. unfolds open_tt.
  pick_fresh X. apply* (@open_tt_rec_type_core T2 0 (typ_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_typ T -> subst_tt Z U T = T.
Proof.
  induction T; simpl; intros; f_equal*.
  case_var*. 
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P n, type P ->
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1).
Proof.
  introv WP. generalize n.
  induction T1; intros k; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_tt_rec_type.
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

Lemma open_te_rec_type_core : forall e j Q i P, i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
   e = open_te_rec i P e.
Proof.
  induction e; intros; simpl in *; inversion H0; f_equal*;
  match goal with H: ?i <> ?j |- ?t = open_tt_rec ?i _ ?t =>
   apply* (@open_tt_rec_type_core t j) end.
Qed.

Lemma open_te_rec_term : forall e U,
  term e -> forall k, e = open_te_rec k U e.
Proof.
  intros e U WF. induction WF; intros; simpl;
    f_equal*; try solve [ apply* open_tt_rec_type ].
  unfolds open_ee. pick_fresh x.
   apply* (@open_te_rec_term_core e1 0 (trm_fvar x)).
  unfolds open_te. pick_fresh X.
   apply* (@open_te_rec_type_core e1 0 (typ_fvar X)).
  unfolds open_ee. pick_fresh x.
   apply* (@open_te_rec_term_core e2 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_te_fresh : forall X U e,
  X \notin fv_trm e -> subst_te X U e = e.
Proof.
  induction e; simpl; intros; f_equal*; autos* subst_tt_fresh.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_te_open_te : forall e T X U, type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T).
Proof.
  intros. unfold open_te. generalize 0.
  induction e; intros; simpls; f_equal*;
  autos* subst_tt_open_tt_rec.
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
  case_nat*. case_nat*.
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
  induction 1; intros; simpl; f_equal*.
  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).

  - unfolds open_te.
    pick_fresh X.
    apply* (@open_ee_rec_type_core e1 0 (typ_fvar X)).

  - unfolds open_ee. pick_fresh x.
    apply* (@open_ee_rec_term_core e2 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)
Lemma subst_ee_fresh : forall x u e,
  x \notin fv_trm e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)
Lemma subst_ee_open_ee : forall t1 t2 u x, term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
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
  induction e; intros; simpl; f_equal*. case_nat*.
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

Lemma subst_tt_type : forall T Z P,
  type T -> type P -> type (subst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* type_all as X. rewrite* subst_tt_open_tt_var.
Qed.

Lemma subst_te_term : forall e Z P,
    term e -> type P -> term (subst_te Z P e)
with subst_te_value : forall e Z P,
    value e -> type P -> value (subst_te Z P e).
Proof.
  - lets: subst_tt_type. induction 1; intros; cbn; auto.
    + apply_fresh* term_abs as x. rewrite* subst_te_open_ee_var.
    + apply_fresh* term_tabs as x.
      rewrite* subst_te_open_te_var.
      rewrite* subst_te_open_te_var.
    + apply_fresh* term_let as x. rewrite* subst_te_open_ee_var.
  - lets: subst_tt_type. induction 1; intros; cbn; auto.
    + apply value_abs.
      inversions H0.
      apply_fresh* term_abs as x.
      rewrite* subst_te_open_ee_var.
    + apply value_tabs. inversion H0.
      apply_fresh* term_tabs as x.
      rewrite* subst_te_open_te_var.
      rewrite* subst_te_open_te_var.
Qed.

Lemma subst_ee_term : forall e1 Z e2,
    term e1 -> term e2 -> term (subst_ee Z e2 e1)
with subst_ee_value : forall e1 Z e2,
    value e1 -> term e2 -> value (subst_ee Z e2 e1).
Proof.
  - induction 1; intros; simpl; auto.
    + case_var*.
    + apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
    + apply_fresh* term_tabs as Y. rewrite* subst_ee_open_te_var.
      rewrite* subst_ee_open_te_var.
    + apply_fresh* term_let as y. rewrite* subst_ee_open_ee_var.
  - induction 1; intros; simpl; auto.
    + apply value_abs. inversions H.
      apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
    + apply value_tabs; inversions H.
      apply_fresh* term_tabs as Y. rewrite* subst_ee_open_te_var.
      rewrite* subst_ee_open_te_var.
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

Lemma values_decidable : forall t,
    term t ->
    (value t \/ ~ (value t)).
  induction t; intro H;
  inversion H; subst; try solve [
                     right; intro Hv; inversion Hv
                   | left; econstructor
                          ].
  - apply IHt1 in H2.
    apply IHt2 in H3.
    destruct H2.
    destruct H3; try solve [
                       left; econstructor; eauto
                     | right; intro Hv; inversion Hv; congruence
                     ].
    right; intro Hv; inversion Hv; congruence. (* why this duplicate is needed??? *)
  - left; econstructor.
    econstructor; eauto.
  - left; econstructor.
    econstructor; eauto.
Qed.

(* Based on: https://github.com/tchajed/strong-induction/blob/master/StrongInduction.v *)
Lemma strong_induction (P : nat -> Prop): (forall m, (forall k, k < m -> P k) -> P m) -> forall n, P n.
  introv IH.
  assert (P 0) as P0.
  apply IH; introv Hfalse; inversion Hfalse.
  assert (forall n m, n <= m -> Nat.pred n <= Nat.pred m) as pred_increasing.
  induction n; cbn; intros.
  apply le_0_n.
  induction H; subst; cbn; eauto.
  destruct m; eauto.
  assert (forall n, (forall m, m <= n -> P m)) as strong_induction_all.
  induction n; intros.
  inversion H; eauto.
  inversion H; eauto using le_S_n.
  eauto using strong_induction_all.
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
  induction T; introv; try solve [cbn; try case_if; cbn; eauto].
Qed.

Require Import Psatz.

Ltac IHap IH := eapply IH; eauto;
                try (unfold open_ee; rewrite <- open_ee_var_preserves_size);
                try (unfold open_te; rewrite <- open_te_var_preserves_size);
                cbn; lia.

Lemma typing_implies_term : forall Σ E e T,
    {Σ, E} ⊢ e ∈ T ->
    term e.
  introv. gen Σ E T.
  gen e.
  pose (P := fun e => (forall (Σ : GADTEnv) (E : ctx) (T : typ), {Σ, E}⊢ e ∈ T -> term e)).
  lets H0: strong_induction_on_term_size P.
  apply H0. unfold P. clear H0 P.
  (* TODO ^ this should be automated *)
  introv IH. introv e_size_n. introv Hetyp.
  inversion Hetyp; subst; eauto; try solve [econstructor; eauto; IHap IH].
  - econstructor; eauto.
    eapply type_from_wft; eauto.
    introv XiL.
    IHap IH.
  - econstructor; eauto.
    introv XiL.
    IHap IH.
  - econstructor; eauto.
    eapply type_from_wft; eauto.
  - econstructor; eauto.
    IHap IH.
    introv xiL.
    IHap IH.
Qed.

Lemma eq_dec_var (x y : var) : x = y \/ x <> y.
  lets: var_compare_eq x y.
  Require Import TLC.LibReflect.
  destruct (var_compare x y);
  rewrite isTrue_eq_if in H;
  case_if; auto.
Qed.
