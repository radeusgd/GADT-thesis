(***************************************************************************
* Adapted from Locally Nameless tutorials
***************************************************************************)

(**

Original tutorial was maed by authors of:
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

It is also highly inspired by formalization of SystemFSub bt Charguéraud: https://www.chargueraud.org/viewcoq.php?sFile=softs%2Fln%2Fsrc%2FFsub_Definitions.v


*)


Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import TLC.LibTactics.
Require Import List.
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
  Print Forall_cons.

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
Print typ_ind'.

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
(* | trm_matchtuple *)
| trm_matchgadt : trm -> (list Clause) -> trm
| trm_let : trm -> trm -> trm
with
Clause : Set :=
| clause (c: GADTConstructor) (e: trm)
.

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
  | typ_gadt tparams name => 1 + (sum (map typ_size tparams)) (* this works with StdLib map but not TLC map... *)
    (*)1 + typlist_size tparams*)
  end
.

(* Fixpoint typlist_size (ts : list typ) : nat := *)
(*   match ts with *)
(*   | nil => 0 *)
(*   | cons h t => typ_size h + typlist_size t *)
(*   end. *)

Fixpoint open_tt_rec (k : nat) (u : typ) (t : typ) {struct t} : typ :=
  match t with
  | typ_bvar i => If k = i then u else (typ_bvar i)
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
  | trm_snd e1 => trm_fst (open_te_rec k u e1)
  | trm_abs T e1    => trm_abs (open_tt_rec k u T) (open_te_rec k u e1)
  | trm_app e1 e2 => trm_app (open_te_rec k u e1) (open_te_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_te_rec (S k) u e1)
  | trm_tapp e1 T => trm_tapp (open_te_rec k u e1) (open_tt_rec k u T)
  | trm_fix T e1 => trm_fix (open_tt_rec k u T) (open_te_rec k u e1)
  | trm_matchgadt e1 clauses => trm_matchgadt (open_te_rec k u e1) (open_te_clauses k u clauses)
  | trm_let e1 e2 => trm_let (open_te_rec k u e1) (open_te_rec k u e2)
  end.

Fixpoint open_ee_rec (k : nat) (u : trm) (e : trm) {struct e} : trm :=
  let fix open_ee_clauses k u (cs : list Clause) : list Clause :=
    match cs with
    | cons (clause c e) t => cons (clause c (open_ee_rec k u e)) (open_ee_clauses k u t)
    | nil => nil
    end in
  match e with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_constructor tparams C e1 => trm_constructor tparams C (open_ee_rec k u e1)
  | trm_unit => trm_unit
  | trm_tuple e1 e2 => trm_tuple (open_ee_rec k u e1) (open_ee_rec k u e2)
  | trm_fst e1 => trm_fst (open_ee_rec k u e1)
  | trm_snd e1 => trm_fst (open_ee_rec k u e1)
  | trm_abs T e1    => trm_abs T (open_ee_rec (S k) u e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k u e1) (open_ee_rec k u e2)
  | trm_tabs e1 => trm_tabs (open_ee_rec k u e1)
  | trm_tapp e1 T => trm_tapp (open_ee_rec k u e1) T
  | trm_fix T e1 => trm_fix T (open_ee_rec k u e1)
  | trm_matchgadt e1 clauses => trm_matchgadt (open_ee_rec k u e1) (open_ee_clauses k u clauses)
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

Lemma open_typlist_test : open_typlist_rec 0 (typ_unit) [typ_bvar 0; typ_tuple (typ_bvar 0) (typ_bvar 1)] = [typ_unit; typ_tuple (typ_unit) (typ_bvar 1)].
  cbv; repeat case_if. auto.
Qed.
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

Lemma open_tt_test : open_tt (typ_all (typ_bvar 1)) (typ_unit) = typ_all typ_unit.
  cbv. case_if*.
Qed.

Lemma open_te_test : open_te (trm_abs (typ_bvar 0) (trm_bvar 0)) (typ_unit) = trm_abs typ_unit (trm_bvar 0).
  cbv. case_if*.
Qed.

Lemma open_ee_test : open_ee (trm_abs (typ_bvar 0) (trm_bvar 1)) (trm_unit) = trm_abs (typ_bvar 0) (trm_unit).
  cbv. case_if*.
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
      type (typ_gadt Tparams Name)
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
    term (trm_tabs e1)
| term_tapp : forall e1 V,
    term e1 ->
    type V ->
    term (trm_tapp e1 V)
| term_fix : forall T e1,
    type T ->
    term e1 ->
    term (trm_fix T e1)
| term_let : forall L e1 e2,
    term e1 ->
    (forall x, x \notin L -> term (e2 open_ee_var x)) ->
    term (trm_let e1 e2)
| term_matchgadt : forall e1 clauses,
    term e1 ->
    (forall cname ce, In (clause cname ce) clauses -> term ce) ->
    term (trm_matchgadt e1 clauses)
.


(* Warning: this is a very early draft of handling the environment *)

Inductive GADTConstructorDef : Set :=
  (* a constructor of type ∀(α...). τ → (β...) T)
     arity specifies how many type parameters (α) there are, they are referred to inside the types by DeBruijn indices
     τ is the type of argument (one arg only, use tuples for more; it can refer to α)
     β are the instantiated type parameters of the returned GADT type (they can refer to α)
     T is the base GADT type name that is returned by this constructor
*)
  GADTconstr (arity : nat) (argtype : typ) (rettype : typ).
(* TODO maybe rettype could be deconstructed to ensure syntactically it's a type application? or e separate well-formedness Prop could be defined *)

(* This env is the signature of the available GADT types, it is Σ in the paper *)
Definition GADTEnv := env (list GADTConstructorDef).
Compute GADTEnv.
(*
Some raw ideas:
- we will need to easily find the constructor signature by name
- GADT type name is contained (implicitly) in the signature

- we could refactor the syntax definition so that everywhere we use a constructor name c, we instead refer to it by T.c where T is the GADT name, this will make checking exhaustivity easier
-- then we could rename constructors of a type T to just numbers, so that first constructor is called T.0, second T.1 etc. this will make things even simpler
--- we could then even require the pattern match to preserve order of constructors (not sure if this helps with anything though, but probably with exhaustivity)
*)

(* TODO translate from Fsub *)

Inductive bind : Set :=
| bind_typ : bind
| bind_var : typ -> bind.

Notation "'withtyp' X" := (X ~ bind_typ) (at level 31, left associativity).
Notation "x ~: T" := (x ~ bind_var T) (at level 31, left associativity).

Definition ctx := env bind.
About binds.
Inductive wft : GADTEnv -> ctx -> typ -> Prop :=
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
| wft_all : forall Σ L E T2,
    (forall X, X \notin L ->
          wft Σ (E & withtyp X) (T2 open_tt_var X)) ->
    wft Σ E (typ_all T2)
| wft_gadt : forall Σ E Tparams Name Def,
    (forall T, In T Tparams -> wft Σ E T) ->
    binds Name Def Σ ->
    wft Σ E (typ_gadt Tparams Name)
.

Inductive okDef : GADTConstructorDef -> Prop :=
  (* TODO are these conditions enough? *)
| ok_def : forall arity argT retT,
    wft empty empty argT -> (* TODO Σ should allow mutually recursive definitions so empty is not right here *)
    wft empty empty retT -> (* TODO extended with arity type args, HOW? *)
    okDef (GADTconstr arity argT retT).


Inductive okGadt : GADTEnv -> Prop :=
| okg_empty : okGadt empty
| okg_push : forall Σ Defs Name,
    okGadt Σ ->
    Name # Σ ->
    (forall Def, In Def Defs -> okDef Def) ->
    okGadt (Σ & Name ~ Defs)
.

Inductive okt : GADTEnv -> ctx -> Prop :=
| okt_empty : forall Σ,
    okGadt Σ ->
    okt Σ empty
| okt_sub : forall Σ E X,
    okt Σ E -> X # E -> okt Σ (E & withtyp X)
| okt_typ : forall Σ E x T,
    okt Σ E -> wft Σ E T -> x # E -> okt Σ (E & (x ~: T)).
