Require Export Zip.
Require Export Definitions.
Require Export TypInduction.
Require Export TLC.LibTactics.
Require Export TLC.LibFset.
Require Export TLC.LibEnv.
Require Import TLC.LibLN.
Require Export Psatz.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
Export List.ListNotations.

#[export] Hint Constructors type term wft typing red value.

#[export] Hint Resolve typing_var typing_app typing_tapp.

Lemma value_is_term : forall e, value e -> term e.
  induction e; intro Hv; inversion Hv; eauto.
Qed.


(** Gathering free names already used in the proofs *)
Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv_trm x) in
  let E := gather_vars_with (fun x : typ => fv_typ x) in
  let F := gather_vars_with (fun x : ctx => dom x \u fv_env x) in
  let G := gather_vars_with (fun x : list var => from_list x) in
  let H := gather_vars_with (fun x : list typ => fv_typs x) in
  let I := gather_vars_with (fun x : typctx => domΔ x \u fv_delta x) in
  constr:(A \u B \u C \u E \u F \u G \u H \u I).

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

Goal forall i j, i <> j -> (match compare i j with | Lt => 0 | Gt => 0 | Eq => 1 end) = 0.
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

(* maybe move strong induction to separate file? *)
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

(* TODO make better names for map_id and ext_in_map *)
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

Ltac crush_open :=
  (try unfold open_tt); (try unfold open_tt_rec); crush_compare.


#[export] Hint Immediate subset_refl subset_empty_l subset_union_weak_l subset_union_weak_r subset_union_2 union_comm union_assoc union_same.

Lemma union_distribute : forall T (A B C : fset T),
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

Ltac copy H :=
  let H' := fresh H in
  let Heq := fresh "EQ" in
  remember H as H' eqn:Heq; clear Heq.

Ltac copyTo H Hto :=
  let H' := fresh Hto in
  let Heq := fresh "EQ" in
  remember H as H' eqn:Heq; clear Heq.

Ltac apply_folding E lemma :=
  expand_env_empty E; apply* lemma; fold_env_empty.

Ltac add_notin x L :=
  let Fr := fresh "Fr" in
  assert (Fr: x \notin L); auto.

Lemma in_right_inv : forall A (x a : A) l,
    List.In x (l |,| [a]) ->
    x = a \/ List.In x l.
  introv Hin.
  lets Hin2: List.in_app_or Hin.
  destruct Hin2 as [Hin2 | Hin2]; auto.
  left.
  inversion~ Hin2.
  contradiction.
Qed.

(* Lemma app_singleton_inv : forall A l1 l2 (a b : A), *)
(*     l1 |,| [a] = l2 |,| [b] -> *)
(*     l1 = l2 /\ a = b. *)
(*   intros. cbn in *. inversions H. *)
(*   auto. *)
(*   induction l1; introv EQ. *)
(*   - cbn in *. *)
(*     destruct l2. *)
(*     + cbn in *. inversion~ EQ. *)
(*     + cbn in *. *)
(*       inversion~ EQ. *)
(*       false* List.app_cons_not_nil. *)
(*   - destruct l2. *)
(*     + inversion ~ EQ. *)
(*       false* List.app_cons_not_nil. *)
(*     + inversions EQ. *)
(*       lets [? ?]: IHl1 H1; subst. *)
(*       auto. *)
(* Qed. *)

(* Lemma subst_match_inv_var : forall Σ Δ A Θ, *)
(*     subst_matches_typctx Σ (Δ |,| [tc_var A]) Θ -> *)
(*     exists T Θ', Θ = (A, T) :: Θ' /\ *)
(*             wft Σ emptyΔ T /\ *)
(*             subst_matches_typctx Σ Δ Θ' /\ *)
(*             A \notin substitution_sources Θ' /\ *)
(*             A \notin domΔ Δ. *)
(*   introv M. *)
(*   inversions M. *)
(*   - false* List.app_cons_not_nil. *)
(*   - lets [? EQvar]: app_singleton_inv H; subst. *)
(*     inversions EQvar. *)
(*     exists T Θ0. splits~. *)
(*   - lets [? EQvar]: app_singleton_inv H; subst. *)
(*     inversion EQvar. *)
(* Qed. *)

(* Lemma subst_match_inv_eq : forall Σ Δ T1 T2 Θ, *)
(*     subst_matches_typctx Σ (Δ |,| [tc_eq (T1 ≡ T2)]) Θ -> *)
(*     subst_matches_typctx Σ Δ Θ /\ *)
(*     (subst_tt' T1 Θ) = (subst_tt' T2 Θ). *)
(*   introv M. *)
(*   inversions M. *)
(*   - false* List.app_cons_not_nil. *)
(*   - lets [? EQ]: app_singleton_inv H; subst. *)
(*     inversions EQ. *)
(*   - lets [? EQ]: app_singleton_inv H; subst. *)
(*     inversions EQ. *)
(*     split~. *)
(* Qed. *)

(* Lemma subst_match_inv_empty : forall Σ Θ, *)
(*     subst_matches_typctx Σ [] Θ -> *)
(*     Θ = []. *)
(*   introv H. *)
(*   inversion~ H; *)
(*     false* List.app_cons_not_nil. *)
(* Qed. *)

(* Ltac invert_subst_match_simple := *)
(*   match goal with *)
(*   | [ H: subst_matches_typctx ?Σ [] ?Θ  |- _ ] => *)
(*     lets: subst_match_inv_empty H; subst *)
(*   | [ H: subst_matches_typctx ?Σ (?Δ |,| [tc_var ?A]) ?Θ  |- _ ] => *)
(*     let Hwft := fresh "SMwft" in *)
(*     let Hmatch := fresh "SMmatch" in *)
(*     let Asrc := fresh "SMAsrc" in *)
(*     let Adom := fresh "SMAdom" in *)
(*     let Th := fresh "Θ" in *)
(*     let U := fresh "U" in *)
(*     lets [U [Th [? [Hwft [Hmatch [Asrc Adom]]]]]]: subst_match_inv_var H; *)
(*     subst *)
(*   | [ H: subst_matches_typctx ?Σ (?Δ |,| [tc_eq (?T1 ≡ ?T2)]) ?Θ  |- _ ] => *)
(*     let Hmatch := fresh "SMmatch" in *)
(*     let Heq := fresh "SMeq" in *)
(*     lets [Hmatch Heq]: subst_match_inv_eq H; *)
(*     subst *)
(*   end. *)

(* Ltac invert_subst_match := *)
(*   match goal with *)
(*   | [ H: subst_matches_typctx ?Σ [] ?Θ  |- _ ] => *)
(*     invert_subst_match_simple *)
(*   | [ H: subst_matches_typctx ?Σ (?Δ |,| [tc_var ?A]) ?Θ  |- _ ] => *)
(*     invert_subst_match_simple *)
(*   | [ H: subst_matches_typctx ?Σ (?Δ |,| [tc_eq (?T1 ≡ ?T2)]) ?Θ  |- _ ] => *)
(*     invert_subst_match_simple *)
(*   | [ H: subst_matches_typctx ?Σ (?Δ |,| [?x]) ?Θ |- _ ] => *)
(*     let A := fresh "A" in *)
(*     let V1 := fresh "V1" in *)
(*     let V2 := fresh "V2" in *)
(*     destruct x as [A | [V1 V2]]; invert_subst_match_simple *)
(*   end. *)

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
      List.length Alphas = len /\ DistinctList Alphas /\ forall A, List.In A Alphas -> A \notin L.
  induction len.
  - exists (@List.nil var). splits*.
    + econstructor.
    + intuition.
  - inversion IHlen as [Alphas' [Hlen [Hdis Hnot]]].
    pick_fresh A.
    exists (List.cons A Alphas').
    splits*.
    + cbn.
      eauto.
    + constructor*.
      intro.
      assert (Hnot2: A \notin from_list Alphas'); eauto.
      apply Hnot2.
      apply* from_list_spec2.
    + introv AiA.
      inversions AiA; eauto.
Qed.

Global Transparent fold_right.

Lemma length_equality : forall A (a : list A),
    LibList.length a = Datatypes.length a.
  induction a; cbn; eauto.
  rewrite <- IHa.
  rewrite length_cons.
  lia.
Qed.

(* stdlib lemma but in TLC version *)
Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
    map g (map f l) = map (fun x => g (f x)) l.
  induction l; cbn; auto.
  repeat rewrite map_cons.
  f_equal.
  auto.
Qed.

Lemma eq_dec_var (x y : var) : x = y \/ x <> y.
  lets: var_compare_eq x y.
  Require Import TLC.LibReflect.
  destruct (var_compare x y);
  rewrite isTrue_eq_if in H;
  case_if; auto.
Qed.

Lemma JMeq_from_eq : forall T (x y : T),
    x = y -> JMeq.JMeq x y.
  introv EQ.
  rewrite EQ. trivial.
Qed.

Lemma split_notin_subset_union : forall T (x : T) A B C,
    A \c B \u C ->
    x \notin B ->
    x \notin C ->
    x \notin A.
  introv Hsub HB HC.
  intro inA.
  lets Hf: Hsub inA.
  rewrite in_union in Hf.
  destruct Hf; eauto.
Qed.

Lemma in_from_list : forall As (x : var),
    x \in from_list As ->
          exists A, List.In A As /\ x = A.
  induction As; introv xin.
  - cbn in xin. exfalso; apply* in_empty_inv.
  - cbn in *.
    fold (from_list As) in xin.
    rewrite in_union in xin.
    destruct xin as [xin | xin].
    + rewrite in_singleton in xin. subst. eauto.
    + lets [A Ain]: IHAs xin.
      exists A. split*.
Qed.

(* Lemma add_types_assoc : forall E F As, *)
(*     (add_types (E & F) As = E & add_types F As)%env. *)
(*   induction As; cbn; eauto. *)
(*   - rewrite IHAs. eauto using concat_assoc. *)
(* Qed. *)

(* Lemma add_types_dom_is_from_list : forall As, *)
(*     (dom (add_types EnvOps.empty As) = from_list As)%env. *)
(*   induction As; cbn. *)
(*   - apply dom_empty. *)
(*   - rewrite dom_concat. *)
(*     rewrite IHAs. *)
(*     rewrite union_comm. *)
(*     unfold from_list. *)
(*     rewrite dom_single. *)
(*     trivial. *)
(* Qed. *)

Lemma fromlist_notin_restated : forall T (X : T) As,
    ~ List.In X As ->
    X \notin from_list As.
  induction As as [|Ah Ats]; introv Hnotin.
  - cbn. eauto.
  - cbn.
    rewrite notin_union.
    constructor.
    + apply notin_singleton.
      intro HF. subst.
      apply Hnotin. eauto with listin.
    + unfold from_list in IHAts.
      apply* IHAts.
      intro HF.
      apply Hnotin. eauto with listin.
Qed.

Lemma env_map_ext_id : forall T (E : env T) (f : T -> T),
    (forall x, f x = x) ->
    EnvOps.map f E = E.
  induction E using env_ind; introv fext;
    autorewrite with rew_env_map; trivial.
  - rewrite* IHE.
    rewrite fext.
    trivial.
Qed.

Lemma env_map_compose : forall A B C (E : env A) (f : A -> B) (g : B -> C) (h : A -> C),
    (forall x, g (f x) = h x) ->
    EnvOps.map g (EnvOps.map f E) = EnvOps.map h E.
  induction E using env_ind; introv Hcomp;
    autorewrite with rew_env_map; trivial.
  - lets IH: IHE f g h.
    rewrite IH; auto.
    rewrite Hcomp. trivial.
Qed.

Ltac clean_empty_Δ :=
  repeat match goal with
         | [ H: context [ emptyΔ |,| ?D ] |- _ ] =>
           rewrite List.app_nil_r in H
         | [ H: context [ ?D |,| emptyΔ ] |- _ ] =>
           rewrite List.app_nil_l in H
         | [ H: context [ [] |,| ?D ] |- _ ] =>
           rewrite List.app_nil_r in H
         | [ H: context [ ?D |,| [] ] |- _ ] =>
           rewrite List.app_nil_l in H
         | [ |- context [ emptyΔ |,| ?D ] ] =>
           rewrite List.app_nil_r
         | [ |- context [ ?D |,| emptyΔ ] ] =>
           rewrite List.app_nil_l
         | [ |- context [ [] |,| ?D ] ] =>
           rewrite List.app_nil_r
         | [ |- context [ ?D |,| [] ] ] =>
           rewrite List.app_nil_l
         end.

Lemma LibList_app_def : forall A (La Lb : list A),
    List.app La Lb = La ++ Lb.
  induction La; intros; cbn.
  - clean_empty_Δ. trivial.
  - rewrite IHLa.
    auto.
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

Lemma list_fold_map : forall (A B : Type) (ls : list A) (f : B -> A -> B) (g : A -> A) (z : B),
    List.fold_left (fun a b => f a b) (List.map g ls) z
    =
    List.fold_left (fun a b => f a (g b)) ls z.
  induction ls; introv; cbn; eauto.
Qed.

Lemma notin_inverse : forall A (x y : A),
    x \notin \{ y } ->
    y \notin \{ x }.
  intros.
  assert (x <> y).
  - intro. subst. apply H. apply in_singleton_self.
  - apply* notin_singleton.
Qed.

Lemma LibList_map : forall T U (l : list T) (f : T -> U),
    List.map f l = LibList.map f l.
  induction l; intros; cbn in *; auto.
  rewrite IHl.
  rewrite LibList.map_cons. auto.
Qed.

Lemma LibList_mem : forall A (x : A) L,
    LibList.mem x L -> List.In x L.
  induction L; introv Hin; cbn in *; inversion Hin; eauto.
Qed.

Lemma subst_tb_many_split : forall Ah Ats Ph Pts F,
    EnvOps.map (subst_tb_many (Ah :: Ats) (Ph :: Pts)) F
    =
    EnvOps.map (subst_tb_many Ats Pts) (EnvOps.map (subst_tb Ah Ph) F).
  intros.
  rewrite map_def.
  rewrite map_map.
  repeat rewrite <- LibList_map.
  cbn.
  apply List.map_ext_in.
  intros.
  destruct a as [? [?]].
  cbn.
  f_equal.
Qed.

Ltac fresh_intros :=
    let envvars := gather_vars in
    intros;
    repeat match goal with
           (* TODO find only uninstantiated *)
      | [ H: ?x \notin ?L |- _ ] =>
        instantiate (1:=envvars) in H
           end.

Lemma union_distributes : forall T (A B C : fset T),
    (A \u B) \n C = (A \n C) \u (B \n C).
  intros.
  apply fset_extens; intros x H.
  - rewrite in_union.
    rewrite in_inter in H.
    destruct H as [HAB HC].
    rewrite in_union in HAB.
    destruct HAB.
    + left.
      rewrite~ in_inter.
    + right.
      rewrite~ in_inter.
  - rewrite in_union in H.
    destruct H as [H | H]; rewrite in_inter in H; destruct H;
      rewrite in_inter;
      split~; rewrite~ in_union.
Qed.

Lemma union_empty : forall T (A B : fset T),
    A \u B = \{} ->
    A = \{} /\ B = \{}.
  intros.
  split;
    apply fset_extens; intros x Hin;
      solve [
          assert (xAB: x \in A \/ x \in B); auto;
          rewrite <- in_union in xAB;
          rewrite H in xAB; auto
        | false* in_empty_inv].
Qed.

Lemma empty_inter_implies_notin : forall T (x : T) A B,
    A \n B = \{} ->
    x \in A -> x \notin B.
  intros.
  intro HF.
  asserts~ AB: (x \in A /\ x \in B).
  rewrite <- in_inter in AB.
  rewrite H in AB.
  apply* in_empty_inv.
Qed.

Ltac fold_subst_src :=
  repeat match goal with
  | [ H: context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} (List.map fst ?Th)] |- _ ] =>
    fold (from_list (List.map fst Th)) in H;
    fold (substitution_sources Th) in H
  | [ |- context[LibList.fold_right (fun (x : var) (acc : fset var) => \{ x} \u acc) \{} (List.map fst ?Th)] ] =>
    fold (from_list (List.map fst Th));
    fold (substitution_sources Th)
  end.

Lemma subset_transitive : forall T (A B C : fset T),
    A \c B ->
    B \c C ->
    A \c C.
  introv AB BC.
  intros x In.
  auto.
Qed.
