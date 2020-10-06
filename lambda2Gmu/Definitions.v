(***************************************************************************
* Adapted from Locally Nameless tutorials
***************************************************************************)

(**

Original tutorial was made by authors of:
  Engineering Formal LibLN
   B. Aydemir, A. Charguéraud, B. C. Pierce, R. Pollack and S. Weirich
   Symposium on Principles of Programming Languages (POPL), January 2008

and its follow-up journal version:

   The Locally Nameless Representation
   Arthur Charguéraud
   Journal of Automated Reasoning (JAR), 2011.

It also reused material prepared for the POPL'08 tutorial:

  "How to write your next POPL paper in Coq"
  organized by B. Aydemir, A. Bohannon, B. Pierce, J. Vaughan,
  D. Vytiniotis, S. Weirich, S. Zdancewic

It is also highly inspired by formalization of SystemFSub by Charguéraud: https://www.chargueraud.org/viewcoq.php?sFile=softs%2Fln%2Fsrc%2FFsub_Definitions.v


*)


Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import TLC.LibTactics.
Require Import List.
Require Import Coq.Init.Nat.
Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

(** * Definitions *)

(* ********************************************************************** *)
(** ** Grammars *)

Definition GADTName : Set := var.
(* I think it's ok to use the same name set for GADT types,
they are always in a distinct syntactic form, so we can distinguish the two uses and softswe don't even have to care if a varaible and GADT type names overlap because they are syntactically distinguished *)

(* See definition below.
We define a GADT in the env as a type with a list of constructors
Each constructor is thus identified by its base typename and its index on that list
*)
Definition GADTConstructor : Set := (GADTName * nat).

(* We will maintain a separate set of DeBruijn indices - one for type variables and one for term variables
So a term Λa. λx: ∀α. Unit. x[a] will be translated to
Λ#. λ#: ∀#. Unit. #0[#0] where #0 at term-level refers to λ and #0 at typelevel refers to Λ
*)

(* pre-type-terms *)
Inductive typ : Set :=
| typ_bvar   : nat -> typ
| typ_fvar   : var -> typ
| typ_unit   : typ
| typ_tuple  : typ -> typ -> typ
| typ_arrow  : typ -> typ -> typ
| typ_all  : typ -> typ
| typ_gadt  : (list typ) -> GADTName -> typ
.

Notation "T1 ==> T2" := (typ_arrow T1 T2) (at level 49, right associativity).
Notation "T1 ** T2" := (typ_tuple T1 T2) (at level 49).
(* Notation "∀( T )" := (typ_all T) (at level 49). *)

Section typ_ind'.
  Variable P : typ -> Prop.
  Hypothesis typ_bvar_case : forall (n : nat), P (typ_bvar n).
  Hypothesis typ_fvar_case : forall (x : var), P (typ_fvar x).
  Hypothesis typ_unit_case : P (typ_unit).
  Hypothesis typ_tuple_case : forall (t1 t2 : typ),
      P t1 -> P t2 -> P (typ_tuple t1 t2).
  Hypothesis typ_arrow_case : forall (t1 t2 : typ),
      P t1 -> P t2 -> P (typ_arrow t1 t2).
  Hypothesis typ_all_case : forall (t1 : typ),
      P t1 -> P (typ_all t1).
 Hypothesis typ_gadt_case : forall (ls : list typ) (n : GADTName),
      Forall P ls -> P (typ_gadt ls n).

  Fixpoint typ_ind' (t : typ) : P t :=
    let fix list_typ_ind (ls : list typ) : Forall P ls :=
        match ls return (Forall P ls) with
        | nil => Forall_nil P
        | cons t' rest =>
          let Pt : P t' := typ_ind' t' in
          let LPt : Forall P rest := list_typ_ind rest in
          (Forall_cons t' Pt LPt)
        end in
    match t with
    | typ_bvar i => typ_bvar_case i
    | typ_fvar x => typ_fvar_case x
    | typ_unit => typ_unit_case
    | typ_tuple t1 t2 => typ_tuple_case (typ_ind' t1) (typ_ind' t2)
    | typ_arrow t1 t2 => typ_arrow_case (typ_ind' t1) (typ_ind' t2)
    | typ_all t1 => typ_all_case (typ_ind' t1)
    | typ_gadt tparams name => typ_gadt_case name (list_typ_ind tparams)
    end.

End typ_ind'.

(* pre-terms *)
Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_constructor : (list typ) -> GADTConstructor -> trm -> trm
| trm_unit : trm
| trm_tuple : trm -> trm -> trm
| trm_fst : trm -> trm
| trm_snd : trm -> trm
| trm_abs  : typ -> trm -> trm
| trm_app  : trm -> trm -> trm
| trm_tabs : trm -> trm
| trm_tapp : trm -> typ -> trm
| trm_fix : typ -> trm -> trm
(* | trm_matchunit *)
(* | trm_matchtuple ( these two add nothing interesting, they may be kept for completeness) *)
(* | trm_matchgadt : trm -> (list Clause) -> trm *)
| trm_let : trm -> trm -> trm
with
Clause : Set :=
| clause (c: GADTConstructor) (e: trm)
.

(* Section trm_ind'. *)
(*   Variable P : trm -> Prop. *)
(*   Hypothesis trm_bvar_case : forall (n : nat), P (trm_bvar n). *)
(*   Hypothesis trm_fvar_case : forall (x : var), P (trm_fvar x). *)
(*   Hypothesis trm_constructor_case : forall (e : trm), *)
(*       P e -> P (trm_fst e). *)
(*   Hypothesis trm_unit_case : P (trm_unit). *)
(*   Hypothesis trm_tuple_case : forall (t1 t2 : trm), *)
(*       P t1 -> P t2 -> P (trm_tuple t1 t2). *)
(*   Hypothesis trm_fst_case : forall (e : trm), *)
(*       P e -> P (trm_fst e). *)
(*   Hypothesis trm_snd_case : forall (e : trm), *)
(*       P e -> P (trm_snd e). *)
(*   Hypothesis trm_abs_case : forall T (e : trm), *)
(*       P e -> P (trm_abs T e). *)
(*   Hypothesis trm_app_case : forall (t1 t2 : trm), *)
(*       P t1 -> P t2 -> P (trm_app t1 t2). *)
(*   Hypothesis trm_tabs_case : forall (e : trm), *)
(*       P e -> P (trm_tabs e). *)
(*   Hypothesis trm_tapp_case : forall (e : trm) T, *)
(*       P e -> P (trm_tapp e T). *)
(*   Hypothesis trm_app_case : forall (t1 t2 : trm), *)
(*       P t1 -> P t2 -> P (trm_app t1 t2). *)
(*   Hypothesis trm_gadt_case : forall (ls : list trm) (n : GADTName), *)
(*       Forall P ls -> P (trm_gadt ls n). *)

(*   Fixpoint trm_ind' (t : trm) : P t := *)
(*     let fix list_trm_ind (ls : list trm) : Forall P ls := *)
(*         match ls return (Forall P ls) with *)
(*         | nil => Forall_nil P *)
(*         | cons t' rest => *)
(*           let Pt : P t' := trm_ind' t' in *)
(*           let LPt : Forall P rest := list_trm_ind rest in *)
(*           (Forall_cons t' Pt LPt) *)
(*         end in *)
(*     match t with *)
(*     | trm_bvar i => trm_bvar_case i *)
(*     | trm_fvar x => trm_fvar_case x *)
(*     | trm_unit => trm_unit_case *)
(*     | trm_tuple t1 t2 => trm_tuple_case (trm_ind' t1) (trm_ind' t2) *)
(*     | trm_arrow t1 t2 => trm_arrow_case (trm_ind' t1) (trm_ind' t2) *)
(*     | trm_all t1 => trm_all_case (trm_ind' t1) *)
(*     | trm_gadt tparams name => trm_gadt_case name (list_trm_ind tparams) *)
(*     end. *)

(* End trm_ind'. *)

(* Coercion trm_bvar : nat >-> trm. *)
(* Coercion trm_fvar : var >-> trm. *)

(** ** Opening *)

(** Opening replaces an index with a term. It corresponds to informal
    substitution for a bound variable, such as in the rule for beta
    reduction. Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened. Opening has no effect for
    terms that are locally closed.

    Natural numbers are just an inductive datatype with two
    constructors: O and S, defined in Coq.Init.Datatypes.

    We make several simplifying assumptions in defining [open_rec].
    First, we assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder.  Second, we
    assume that this function is initially called with index zero and
    that zero is the only unbound index in the term.  This eliminates
    the need to possibly subtract one in the case of indices.

    There is no need to worry about variable capture because bound
    variables are indices.
 *)
Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | nil => O
    | cons h t => plus h (sum t)
  end.

Fixpoint typ_size (t : typ) : nat :=
  (* let fix typlist_size (ts : list typ) : nat := *)
  (*   match ts with *)
  (*   | nil => 0 *)
  (*   | cons h t => typ_size h + typlist_size t *)
  (*   end in *)
  match t with
  | typ_bvar i => 1
  | typ_fvar x => 1
  | typ_unit => 1
  | typ_tuple t1 t2 => 1 + typ_size t1 + typ_size t2
  | typ_arrow t1 t2 => 1 + typ_size t1 + typ_size t2
  | typ_all t1 => 1 + typ_size t1
  | typ_gadt tparams name => 1 + (sum (map typ_size tparams))
    (*)1 + typlist_size tparams*)
  end
.

(* Fixpoint typlist_size (ts : list typ) : nat := *)
(*   match ts with *)
(*   | nil => 0 *)
(*   | cons h t => typ_size h + typlist_size t *)
(*   end. *)

Fixpoint trm_size (e : trm) : nat :=
  match e with
  | trm_bvar i    => 1
  | trm_fvar x    => 1
  | trm_constructor tparams C e1 => 1 + trm_size e1 (* TODO typs? *)
  | trm_unit => 1
  | trm_tuple e1 e2 => 1 + trm_size e1 + trm_size e2
  | trm_fst e1 => 1 + trm_size e1
  | trm_snd e1 => 1 + trm_size e1
  | trm_abs T e1    => 1 + trm_size e1 (* TODO: typ? *)
  | trm_app e1 e2 => 1 + trm_size e1 + trm_size e2
  | trm_tabs e1 => 1 + trm_size e1
  | trm_tapp e1 T => 1 + trm_size e1
  | trm_fix T e1 => 1 + trm_size e1
  (* | trm_matchgadt e1 clauses =>  *)
  | trm_let e1 e2 => 1 + trm_size e1 + trm_size e2
  end.

Fixpoint open_tt_rec (k : nat) (u : typ) (t : typ) {struct t} : typ :=
  match t with
  (* | typ_bvar i => If (k < i) then (typ_bvar (i - 1)) else If k = i then u else (typ_bvar i) (* TODO shouldnt some decrement happen here?; YES *) *)
  | typ_bvar i => match Nat.compare k i with
                 | Lt => typ_bvar (i-1)
                 | Eq => u
                 | Gt => typ_bvar i
                 end
  (*                                       (* We only decrement type variables though as values are substituted one by one only *) *)
  | typ_fvar x => typ_fvar x
  | typ_unit => typ_unit
  | typ_tuple t1 t2 => typ_tuple (open_tt_rec k u t1) (open_tt_rec k u t2)
  | typ_arrow t1 t2 => typ_arrow (open_tt_rec k u t1) (open_tt_rec k u t2)
  | typ_all t1 => typ_all (open_tt_rec (S k) u t1)
  | typ_gadt tparams name => typ_gadt (map (open_tt_rec k u) tparams) name
end.

Definition open_typlist_rec k u (ts : list typ) : list typ := map (open_tt_rec k u) ts.

Fixpoint open_te_rec (k : nat) (u : typ) (t : trm) {struct t} : trm :=
  let fix open_te_clauses k u (cs : list Clause) : list Clause :=
    match cs with
    | cons (clause c e) t => cons (clause c (open_te_rec k u e)) (open_te_clauses k u t)
    | nil => nil
    end in
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_constructor tparams C e1 => trm_constructor (open_typlist_rec k u tparams) C (open_te_rec k u e1)
  | trm_unit => trm_unit
  | trm_tuple e1 e2 => trm_tuple (open_te_rec k u e1) (open_te_rec k u e2)
  | trm_fst e1 => trm_fst (open_te_rec k u e1)
  | trm_snd e1 => trm_snd (open_te_rec k u e1)
  | trm_abs T e1    => trm_abs (open_tt_rec k u T) (open_te_rec k u e1)
  | trm_app e1 e2 => trm_app (open_te_rec k u e1) (open_te_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_te_rec (S k) u e1)
  | trm_tapp e1 T => trm_tapp (open_te_rec k u e1) (open_tt_rec k u T)
  | trm_fix T e1 => trm_fix (open_tt_rec k u T) (open_te_rec k u e1)
  (* | trm_matchgadt e1 clauses => trm_matchgadt (open_te_rec k u e1) (open_te_clauses k u clauses) *)
  | trm_let e1 e2 => trm_let (open_te_rec k u e1) (open_te_rec k u e2)
  end.

Fixpoint open_ee_rec (k : nat) (u : trm) (e : trm) {struct e} : trm :=
  let fix open_ee_clauses k u (cs : list Clause) : list Clause :=
    match cs with
    | cons (clause c e) t => cons (clause c (open_ee_rec k u e)) (open_ee_clauses k u t)
    | nil => nil
    end in
  match e with
  (* | trm_bvar i    => If k = i then u else (trm_bvar i) *)
  | trm_bvar i    => if (k =? i) then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_constructor tparams C e1 => trm_constructor tparams C (open_ee_rec k u e1)
  | trm_unit => trm_unit
  | trm_tuple e1 e2 => trm_tuple (open_ee_rec k u e1) (open_ee_rec k u e2)
  | trm_fst e1 => trm_fst (open_ee_rec k u e1)
  | trm_snd e1 => trm_snd (open_ee_rec k u e1)
  | trm_abs T e1    => trm_abs T (open_ee_rec (S k) u e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k u e1) (open_ee_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_ee_rec k u e1)
  | trm_tapp e1 T => trm_tapp (open_ee_rec k u e1) T
  | trm_fix T e1 => trm_fix T (open_ee_rec (S k) u e1)
  (* | trm_matchgadt e1 clauses => trm_matchgadt (open_ee_rec k u e1) (open_ee_clauses k u clauses) *)
  | trm_let e1 e2 => trm_let (open_ee_rec k u e1) (open_ee_rec (S k) u e2)
  end.
(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
    Recall that the coercions above let us write [x] in place of
    [(fvar x)].
*)
Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te t U := open_te_rec 0 U t.
Definition open_ee t u := open_ee_rec 0 u t.

(* (** We define notations for [open_rec] and [open]. *) *)

(* Notation "{ k ~> u } t" := (open_rec k u t) (at level 67). *)
(* Notation "t ^^ u" := (open t u) (at level 67). *)

(* (** We also define a notation for the specialization of [open] to *)
(*     the case where the argument is a free variable. This notation *)
(*     is not needed when [trm_fvar] is declared as a coercion like *)
(*     we do in this tutorial, but it is very handy when we don't want *)
(*     to have such a coercion. (Coercions are very convenient for *)
(*     simple developments, but they can make things very obscur when *)
(*     it comes to scaling up to larger developments.)  *) *)

(* Notation "t ^ x" := (open t (trm_fvar x)). *)

Notation "T 'open_tt_var' X" := (open_tt T (typ_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (typ_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(* Definition open_tt_many (args : list typ) (T : typ) := fold_left open_tt args T. *)
(* Definition open_tt_many_var (args : list var) (T : typ) := fold_left (fun typ v => open_tt typ (typ_fvar v)) args T. *)

Fixpoint open_tt_many (args : list typ) (T : typ) :=
  match args with
  | ha :: ta => open_tt_many ta (open_tt T ha)
  | [] => T
  end.

Definition open_tt_many_var (args : list var) (T : typ) := open_tt_many (map typ_fvar args) T.

Definition open_te_many (args : list typ) (e : trm) := fold_left open_te args e.
(* Fixpoint open_tt_many (T : typ) (args : list typ) : typ := *)
(*   match args with *)
(*   | [] => T *)
(*   | h :: t => open_tt_many (open_tt T h) t *)
(*   end. *)


Lemma open_tt_test : open_tt (typ_all (typ_bvar 1)) (typ_unit) = typ_all typ_unit.
  cbv. auto.
Qed.

Lemma open_te_test : open_te (trm_abs (typ_bvar 0) (trm_bvar 0)) (typ_unit) = trm_abs typ_unit (trm_bvar 0).
  cbv. auto.
Qed.

Lemma open_ee_test : open_ee (trm_abs (typ_bvar 0) (trm_bvar 1)) (trm_unit) = trm_abs (typ_bvar 0) (trm_unit).
  cbv. auto.
Qed.

Lemma open_typlist_test : open_typlist_rec 0 (typ_unit) [typ_bvar 0; typ_tuple (typ_bvar 0) (typ_bvar 1)] = [typ_unit; typ_tuple (typ_unit) (typ_bvar 0)].
  cbv; repeat case_if. auto.
Qed.

Axiom T : var.
(* Lemma open_tt_many_test : open_tt_many [typ_unit; typ_fvar T] (typ_tuple (typ_bvar 0) (typ_bvar 1)) = typ_tuple typ_unit (typ_fvar T). *)
(*   cbv. auto. *)
(* Qed. *)
Lemma open_tt_many_test : open_tt_many [typ_unit; typ_fvar T] (typ_tuple (typ_bvar 0) (typ_bvar 1)) = typ_tuple typ_unit (typ_fvar T).
  cbv. auto.
Qed.

Lemma open_te_many_test : open_te_many [typ_unit; typ_fvar T] (trm_abs (typ_tuple (typ_bvar 0) (typ_bvar 1)) (trm_bvar 0)) = (trm_abs (typ_tuple typ_unit (typ_fvar T)) (trm_bvar 0)).
  cbv. auto.
Qed.

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_unit :
      type typ_unit
  | type_tuple : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_tuple T1 T2)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T2,
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (typ_all T2)
  | type_gadt : forall Tparams Name,
      (forall Tparam, In Tparam Tparams -> type Tparam) ->
       type (typ_gadt Tparams Name) (* TODO shouldn't this check the constructor arity already? *)
.

Inductive term : trm -> Prop :=
| term_var : forall x,
    term (trm_fvar x)
| term_constructor : forall Tparams Name e1,
    term e1 ->
    (forall Tparam, In Tparam Tparams -> type Tparam) ->
    term (trm_constructor Tparams Name e1)
| term_unit : term trm_unit
| term_tuple : forall e1 e2,
    term e1 ->
    term e2 ->
    term (trm_tuple e1 e2)
| term_fst : forall e1,
    term e1 ->
    term (trm_fst e1)
| term_snd : forall e1,
    term e1 ->
    term (trm_snd e1)
| term_abs : forall L V e1,
    type V ->
    (forall x, x \notin L -> term (e1 open_ee_var x)) ->
    term (trm_abs V e1)
| term_app : forall e1 e2,
    term e1 ->
    term e2 ->
    term (trm_app e1 e2)
| term_tabs : forall L e1,
    (forall X, X \notin L -> term (e1 open_te_var X)) ->
    (forall X, X \notin L -> value (e1 open_te_var X)) -> (* this has be separated to make some induction proofs work. we may consider completely splitting the values requirements to a separate property *)
    term (trm_tabs e1)
| term_tapp : forall v1 V,
    term v1 ->
    type V ->
    term (trm_tapp v1 V)
| term_fix : forall L T v1,
    type T ->
    (forall x, x \notin L -> term (v1 open_ee_var x)) ->
    (forall x, x \notin L -> value (v1 open_ee_var x)) -> (* this has be separated to make some induction proofs work. we may consider completely splitting the values requirements to a separate property *)
    term (trm_fix T v1)
| term_let : forall L e1 e2,
    term e1 ->
    (forall x, x \notin L -> term (e2 open_ee_var x)) ->
    term (trm_let e1 e2)
(* | term_matchgadt : forall e1 clauses, *)
(*     term e1 -> *)
(*     (forall cname ce, In (clause cname ce) clauses -> term ce) -> *)
(*     term (trm_matchgadt e1 clauses) *)
with
value : trm -> Prop :=
| value_abs : forall V e1, term (trm_abs V e1) ->
                      value (trm_abs V e1)
| value_tabs : forall e1, term (trm_tabs e1) ->
                     value (trm_tabs e1)
| value_unit : value (trm_unit)
                     (* TODO value_fvar ??? this is problematic as we have x-vars and f-vars, do we need to differentiate them? *)
| value_tuple : forall e1 e2,
    value e1 ->
    value e2 ->
    value (trm_tuple e1 e2)
| value_gadt : forall Tparams Name e1,
    term (trm_constructor Tparams Name e1) ->
    value e1 ->
    value (trm_constructor Tparams Name e1)
.



(* Warning: this is a very early draft of handling the environment *)

Inductive GADTConstructorDef : Set :=
  (* a constructor of type ∀(α...). τ → (β...) T)
     arity specifies how many type parameters (α) there are, they are referred to inside the types by DeBruijn indices
     τ is the type of argument (one arg only, use tuples for more; it can refer to α)
     β are the instantiated type parameters of the returned GADT type (they can refer to α) - βs are represented by rettypes
     T is the base GADT type name that is returned by this constructor, it is not included in the constructor definition as it is implicit from where this definition is
   *)
  GADTconstr (arity : nat) (argtype : typ) (rettypes : list typ).

Inductive GADTDef : Set :=
  GADT (arity : nat) (constructors : list GADTConstructorDef).

(* This env is the signature of the available GADT types, it is Σ in the paper *)
Definition GADTEnv := env GADTDef.
(*
Some raw ideas:
- we will need to easily find the constructor signature by name
- GADT type name is contained (implicitly) in the signature

- we could refactor the syntax definition so that everywhere we use a constructor name c, we instead refer to it by T.c where T is the GADT name, this will make checking exhaustivity easier
-- then we could rename constructors of a type T to just numbers, so that first constructor is called T.0, second T.1 etc. this will make things even simpler
--- we could then even require the pattern match to preserve order of constructors (not sure if this helps with anything though, but probably with exhaustivity)
*)

Inductive bind : Set :=
| bind_typ : bind
| bind_var : typ -> bind.

Notation "'withtyp' X" := (X ~ bind_typ) (at level 31, left associativity).
Notation "x ~: T" := (x ~ bind_var T) (at level 27, left associativity).

Unset Implicit Arguments.
Definition ctx := env bind.
About binds.
Inductive wft : GADTEnv -> env bind -> typ -> Prop :=
| wft_unit : forall Σ E,
    wft Σ E typ_unit
| wft_var : forall Σ E X,
    binds X (bind_typ) E ->
    wft Σ E (typ_fvar X)
| wft_arrow : forall Σ E T1 T2,
    wft Σ E T1 ->
    wft Σ E T2 ->
    wft Σ E (typ_arrow T1 T2)
| wft_tuple : forall Σ E T1 T2,
    wft Σ E T1 ->
    wft Σ E T2 ->
    wft Σ E (typ_tuple T1 T2)
| wft_all : forall (L : fset var) Σ E T2,
    (forall X, X \notin L ->
          wft Σ (E & withtyp X) (T2 open_tt_var X)) ->
    wft Σ E (typ_all T2)
| wft_gadt : forall Σ E Tparams Name Arity Defs,
    (forall T, In T Tparams -> wft Σ E T) ->
    binds Name (GADT Arity Defs) Σ ->
    length Tparams = Arity ->
    wft Σ E (typ_gadt Tparams Name)
.

Definition add_types (E : ctx) (args : list var) :=
  fold_left (fun E T => E & withtyp T) args E.

(* Inductive DistinctFset : fset var -> Prop := *)
(* | distinct_empty : DistinctFset \{} *)
(* | distinct_append : forall h t, h \notin t -> DistinctFset t -> DistinctFset (\{ h } \u t). *)

(* Definition DistinctList (L : list var) : Prop := DistinctFset (from_list L). *)
Inductive DistinctList : list var -> Prop :=
| distinctive_empty : DistinctList []
| distinctive_cons : forall h t, (~ List.In h t) -> DistinctList (h :: t).

Inductive okConstructorDef : GADTEnv ->  nat -> GADTConstructorDef -> Prop :=
(* TODO are these conditions enough? *)
| ok_constr_def : forall Tarity Carity argT Σ L retTs,
    (* TODO the L may need to be moved inside the Alphas-props *)
    length retTs = Tarity ->
    (forall Alphas E,
        DistinctList Alphas ->
        length Alphas = Carity ->
        (forall alpha, In alpha Alphas -> alpha \notin L) ->
        wft Σ (add_types E Alphas) (open_tt_many_var Alphas argT)
    ) ->
    (forall Alphas E,
        DistinctList Alphas ->
        length Alphas = Carity ->
        (forall alpha, In alpha Alphas -> alpha \notin L) ->
        (forall retT,
            In retT retTs ->
            wft Σ (add_types E Alphas) (open_tt_many_var Alphas retT))
    ) ->
    (* this is a peculiar situation because normally the de bruijn type vars would be bound to a forall, but here we can't do that directly, we don't want to use free variables either, maybe a separate well formed with N free type vars judgement will help? *)
    okConstructorDef Σ Tarity (GADTconstr Carity argT retTs).

Definition okGadt (Σ : GADTEnv) : Prop :=
  ok Σ /\
  forall Name Arity Defs,
    binds Name (GADT Arity Defs) Σ ->
    (forall Def,
        In Def Defs ->
        okConstructorDef Σ Arity Def).

(* Inductive okGadt : GADTEnv -> Prop := *)
(* | okg_empty : okGadt empty *)
(* | okg_push : forall Σ Defs Name arity, *)
(*     okGadt Σ -> *)
(*     Name # Σ -> *)
(*     (forall Def, *)
(*         In Def Defs -> *)
(*         okConstructorDef (Σ & Name ~ (GADT arity Defs)) arity Def) -> *)
(*     okGadt (Σ & Name ~ GADT arity Defs) *)
(* . *)

Inductive okt : GADTEnv -> ctx -> Prop :=
| okt_empty : forall Σ,
    okGadt Σ ->
    okt Σ empty
| okt_sub : forall Σ E X,
    okt Σ E -> X # E -> okt Σ (E & withtyp X)
| okt_typ : forall Σ E x T,
    okt Σ E -> wft Σ E T -> x # E -> okt Σ (E & x ~: T).


Reserved Notation "{ Σ , E }  ⊢ t ∈ T" (at level 0, Σ at level 99, T at level 69).

Inductive typing : GADTEnv -> ctx -> trm -> typ -> Prop :=
  (* TODO typing_eq *)
| typing_unit : forall Σ E,
    okt Σ E ->
    {Σ, E} ⊢ trm_unit ∈ typ_unit
| typing_var : forall Σ E x T,
    binds x (bind_var T) E ->
    okt Σ E ->
    {Σ, E} ⊢ (trm_fvar x) ∈ T
| typing_cons : forall Σ E Ts Name Ctor e1 Tarity Ctors Carity CargType CretTypes Targ Tret,
    {Σ, E} ⊢ e1 ∈ Targ ->
    binds Name (GADT Tarity Ctors) Σ ->
    nth_error Ctors Ctor = Some (GADTconstr Carity CargType CretTypes) ->
    length Ts = Carity ->
    Targ = open_tt_many Ts CargType ->
    (forall T, In T Ts -> wft Σ E T) ->
    (* alternatively: Tret = open_tt_many (typ_gadt (List.map (fun T => open_tt_many T Ts) CretTypes) Name) Ts -> *)
    Tret = open_tt_many Ts (typ_gadt CretTypes Name) ->
    {Σ, E} ⊢ trm_constructor Ts (Name, Ctor) e1 ∈ Tret
| typing_abs : forall L Σ E V e1 T1,
    (forall x, x \notin L -> {Σ, E & x ~: V} ⊢ e1 open_ee_var x ∈ T1) ->
    {Σ, E} ⊢ trm_abs V e1 ∈ V ==> T1
| typing_app : forall Σ E T1 T2 e1 e2,
    {Σ, E} ⊢ e2 ∈ T1 ->
    {Σ, E} ⊢ e1 ∈ T1 ==> T2 ->
    {Σ, E} ⊢ trm_app e1 e2 ∈ T2
| typing_tabs : forall L Σ E e1 T1,
    (forall X, X \notin L -> (* TODO consider splitting value and term as this case may be problematic ? *)
          value (e1 open_te_var X)) ->
    (forall X, X \notin L ->
          {Σ, E & withtyp X} ⊢ (e1 open_te_var X) ∈ (T1 open_tt_var X)) ->
    {Σ, E} ⊢ (trm_tabs e1) ∈ typ_all T1
| typing_tapp : forall Σ E e1 T1 T T',
    {Σ, E} ⊢ e1 ∈ typ_all T1 ->
    wft Σ E T ->
    T' = open_tt T1 T ->
    {Σ, E} ⊢ trm_tapp e1 T ∈ T'
| typing_tuple : forall Σ E T1 T2 e1 e2,
    {Σ, E} ⊢ e1 ∈ T1 ->
    {Σ, E} ⊢ e2 ∈ T2 ->
    {Σ, E} ⊢ trm_tuple e1 e2 ∈ T1 ** T2
| typing_fst : forall Σ E T1 T2 e1,
    {Σ, E} ⊢ e1 ∈ T1 ** T2 ->
    {Σ, E} ⊢ trm_fst e1 ∈ T1
| typing_snd : forall Σ E T1 T2 e1,
    {Σ, E} ⊢ e1 ∈ T1 ** T2 ->
    {Σ, E} ⊢ trm_snd e1 ∈ T2
| typing_fix : forall L Σ E T v,
    (forall x, x \notin L -> value (v open_ee_var x)) ->
    (forall x, x \notin L -> {Σ, E & x ~: T} ⊢ (v open_ee_var x) ∈ T) ->
    {Σ, E} ⊢ trm_fix T v ∈ T
| typing_let : forall L Σ E V T2 e1 e2,
    {Σ, E} ⊢ e1 ∈ V ->
    (forall x, x \notin L -> {Σ, E & x ~: V} ⊢ e2 open_ee_var x ∈ T2) ->
    {Σ, E} ⊢ trm_let e1 e2 ∈ T2
where "{ Σ , E } ⊢ t ∈ T" := (typing Σ E t T).

Reserved Notation "e1 --> e2" (at level 49).
Inductive red : trm -> trm -> Prop :=
| red_beta : forall T e1 v2 e',
    term (trm_abs T e1) ->
    value v2 ->
    e' = open_ee e1 v2 ->
    trm_app (trm_abs T e1) v2 --> e'
| red_tbeta : forall e1 T e',
    term (trm_tabs e1) ->
    type T ->
    e' = open_te e1 T ->
    trm_tapp (trm_tabs e1) T --> e'
| red_letbeta : forall v1 e2 e',
    term (trm_let v1 e2) ->
    value v1 ->
    e' = open_ee e2 v1 ->
    trm_let v1 e2 --> e'
| red_fst : forall v1 v2,
    value (trm_tuple v1 v2) ->
    trm_fst (trm_tuple v1 v2) --> v1
| red_snd : forall v1 v2,
    value (trm_tuple v1 v2) ->
    trm_snd (trm_tuple v1 v2) --> v2
| red_fix : forall T v e',
    term (trm_fix T v) ->
    e' = open_ee v (trm_fix T v) ->
    trm_fix T v --> e'
| ered_app_1 : forall e1 e1' e2,
    e1 --> e1' ->
    trm_app e1 e2 --> trm_app e1' e2
| ered_constructor : forall l Ctor e e',
    e --> e' ->
    trm_constructor l Ctor e --> trm_constructor l Ctor e'
| ered_app_2 : forall v1 e2 e2',
    value v1 ->
    e2 --> e2' ->
    trm_app v1 e2 --> trm_app v1 e2'
| ered_tapp : forall e1 e1' T,
    type T ->
    e1 --> e1' ->
    trm_tapp e1 T --> trm_tapp e1' T
| ered_fst : forall e e',
    e --> e' ->
    trm_fst e --> trm_fst e'
| ered_snd : forall e e',
    e --> e' ->
    trm_snd e --> trm_snd e'
| ered_tuple_fst : forall e1 e2 e1',
    e1 --> e1' ->
    trm_tuple e1 e2 --> trm_tuple e1' e2
| ered_tuple_snd : forall v1 e2 e2',
    value v1 ->
    e2 --> e2' ->
    trm_tuple v1 e2 --> trm_tuple v1 e2'
| ered_let : forall e1 e2 e1',
    e1 --> e1' ->
    trm_let e1 e2 --> trm_let e1' e2
where "e1 --> e2" := (red e1 e2).

Fixpoint fv_typ (T : typ) {struct T} : vars :=
  match T with
  | typ_bvar J => \{}
  | typ_fvar X => \{X}
  | typ_unit   => \{}
  | T1 ** T2   => fv_typ T1 \u fv_typ T2
  | T1 ==> T2   => fv_typ T1 \u fv_typ T2
  | typ_all T1 => fv_typ T1
  | typ_gadt Ts _ => fold_left (fun fv T => fv \u fv_typ T) Ts \{}
  end.

(* TODO shall we differentiate free type and term variables? *)

Fixpoint fv_trm (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i => \{}
  | trm_fvar x => \{x}
  | trm_unit   => \{}
  | trm_tuple e1 e2 => fv_trm e1 \u fv_trm e2
  | trm_fst e1 => fv_trm e1
  | trm_snd e1 => fv_trm e1
  | trm_abs T1 e1 => fv_typ T1 \u fv_trm e1
  | trm_app e1 e2 => fv_trm e1 \u fv_trm e2
  | trm_tabs e1 => fv_trm e1
  | trm_tapp e1 T1 => fv_typ T1 \u fv_trm e1
  | trm_fix T1 e1 => fv_typ T1 \u fv_trm e1
  | trm_let e1 e2 => fv_trm e1 \u fv_trm e2
  (* | trm_matchgadt _ _ => \{} (* TODO GADT support *) *)
  | trm_constructor Ts _ e1 =>
    fold_left (fun fv T => fv \u fv_typ T) Ts (fv_trm e1)
  end.

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J => typ_bvar J
  (* | typ_fvar X => If X = Z then U else (typ_fvar X) *)
  | typ_fvar X => If X = Z then U else (typ_fvar X)
  | typ_unit   => typ_unit
  | T1 ** T2   => subst_tt Z U T1 ** subst_tt Z U T2
  | T1 ==> T2   => subst_tt Z U T1 ==> subst_tt Z U T2
  | typ_all T1 => typ_all (subst_tt Z U T1)
  | typ_gadt Ts Name => typ_gadt (map (subst_tt Z U) Ts) Name
  end.

Fixpoint subst_te (Z : var) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i => trm_bvar i
  | trm_fvar x => trm_fvar x
  | trm_unit   => trm_unit
  | trm_tuple e1 e2 => trm_tuple (subst_te Z U e1) (subst_te Z U e2)
  | trm_fst e1 => trm_fst (subst_te Z U e1)
  | trm_snd e1 => trm_snd (subst_te Z U e1)
  | trm_abs T1 e1 => trm_abs (subst_tt Z U T1) (subst_te Z U e1)
  | trm_app e1 e2 => trm_app (subst_te Z U e1) (subst_te Z U e2)
  | trm_tabs e1 => trm_tabs (subst_te Z U e1)
  | trm_tapp e1 T1 => trm_tapp (subst_te Z U e1) (subst_tt Z U T1)
  | trm_fix T1 e1 => trm_fix (subst_tt Z U T1) (subst_te Z U e1)
  | trm_let e1 e2 => trm_let (subst_te Z U e1) (subst_te Z U e2)
  (* | trm_matchgadt _ _ => e (* TODO GADT support *) *)
  | trm_constructor Ts N e1 => trm_constructor (map (subst_tt Z U) Ts) N (subst_te Z U e1)
  end.

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i => trm_bvar i
  | trm_fvar x => If x = z then u else (trm_fvar x)
  | trm_unit   => trm_unit
  | trm_tuple e1 e2 => trm_tuple (subst_ee z u e1) (subst_ee z u e2)
  | trm_fst e1 => trm_fst (subst_ee z u e1)
  | trm_snd e1 => trm_snd (subst_ee z u e1)
  | trm_abs T1 e1 => trm_abs T1 (subst_ee z u e1)
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm_tabs e1 => trm_tabs (subst_ee z u e1)
  | trm_tapp e1 T1 => trm_tapp (subst_ee z u e1) T1
  | trm_fix T1 e1 => trm_fix T1 (subst_ee z u e1)
  | trm_let e1 e2 => trm_let (subst_ee z u e1) (subst_ee z u e2)
  (* | trm_matchgadt _ _ => e (* TODO GADT support *) *)
  | trm_constructor Ts N e1 => trm_constructor Ts N (subst_ee z u e1)
  end.

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_typ => bind_typ
  | bind_var T => bind_var (subst_tt Z P T)
  end.

Definition progress := forall Σ e T,
    {Σ, empty} ⊢ e ∈ T ->
    (value e) \/ (exists e', e --> e').

Definition preservation := forall Σ e T e',
    {Σ, empty} ⊢ e ∈ T ->
    e --> e' ->
    {Σ, empty} ⊢ e' ∈ T.


Lemma list_quantification : forall A (L : list A) (P : A -> Prop),
    (forall x, In x L -> P x) <-> Forall P L.
  intuition.
  - induction L.
    + econstructor.
    + econstructor.
      * apply H.
        constructor*.
      * apply IHL.
        intros. apply H.
        apply* in_cons.
  - induction L.
    + inversion H0.
    + destruct (in_inv H0); subst.
      * inversion* H.
      * inversions H. apply* IHL.
Qed.

Fixpoint zip {A B} (As : list A) (Bs : list B) : list (A * B) :=
  match (As, Bs) with
  | ([], []) => []
  | (ha :: ta, hb :: tb) => (ha, hb) :: (zip ta tb)
  | _ => []
  end.

Lemma zip_eq_len : forall A B (As : list A) (Bs : list B),
    length As = length Bs ->
    length (zip As Bs) = length As.
  intros. gen Bs.
  induction As; intros.
  - cbn. destruct Bs; cbn; auto.
  - destruct Bs.
    + inversion H.
    + cbn. intuition.
Qed.
