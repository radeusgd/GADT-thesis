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
Import List.ListNotations.
Require Import Zip.


Inductive DistinctList : list var -> Prop :=
| distinctive_empty : DistinctList []
| distinctive_cons : forall h t, (~ List.In h t) -> DistinctList t -> DistinctList (h :: t).

(** * Types *)

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

(** * Terms *)


(* I propose a simple rewrite of original syntax:
since we assume all matches are exhaustive, instead of specifying the GADT name in each branch and specifying which constructor we refer to,
we specify inside of the *match* which GADT we plan to match and then
each case corresponds to consecutive constructors:
i.e. first case matches first constructor, second one second etc.
Checking if the match is exhaustive in this form is as simple as checking
length cases = length constructors

Another thing to consider is that originally the clauses would look like this:
constructor[T1, T2, ..., Tm](x) => expr[where T1,... and x are bound]
as we use DeBruijn indices for bound variables, we do not use these names, so we can remove them
BUT we keep the length of the list of types to be bound, so the new form is following
case (constructor id is implicit from order) [M] => expr with 1 bound value variable and M bound type variables.
This M is then checked in typing if it is consistent with constructor arguments count.
We need to know M in syntax to make properties like 'closed type' not dependent on typing environment.
It is quite expected, since we also have this information in the original syntax (the length of list of type variables to bind).

Overall, an expression
case e of
| c1[T1,...Tm1](x1) => e1
| ...
| cn[Tn,...Tmn](xn) => en
where c1, ..., cn are constructors of type TG (as explained in other notes, we do not allow matches that mix types)

becomes
case e matching TG of
| [M1] => e1'
| ...
| [Mn] => en'

where ei' := ei[ T1 -> @0, ..., Tm -> @(m-1), xi -> #0 ]
TODO: or is type translation order in reverse?
 *)

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
| trm_matchgadt : trm -> GADTName -> (list Clause) -> trm
| trm_let : trm -> trm -> trm
with
(* Clause : Set := *)
(* | clause (c: GADTConstructor) (e: trm) *)
Clause : Set :=
| clause (clArity : nat) (e : trm)
.

Definition clauseArity (c : Clause) : nat :=
  match c with
  | clause n _ => n
  end.

Definition clauseTerm (c : Clause) : trm :=
  match c with
  | clause _ t => t
  end.

Section trm_ind'.
  Variable P : trm -> Prop.
  Hypothesis trm_bvar_case : forall (n : nat), P (trm_bvar n).
  Hypothesis trm_fvar_case : forall (x : var), P (trm_fvar x).
  Hypothesis trm_constructor_case : forall (e : trm) (Ts : list typ) (GADTC : GADTConstructor),
      P e -> P (trm_constructor Ts GADTC e).
  Hypothesis trm_unit_case : P (trm_unit).
  Hypothesis trm_tuple_case : forall (t1 t2 : trm),
      P t1 -> P t2 -> P (trm_tuple t1 t2).
  Hypothesis trm_fst_case : forall (e : trm),
      P e -> P (trm_fst e).
  Hypothesis trm_snd_case : forall (e : trm),
      P e -> P (trm_snd e).
  Hypothesis trm_abs_case : forall T (e : trm),
      P e -> P (trm_abs T e).
  Hypothesis trm_app_case : forall (t1 t2 : trm),
      P t1 -> P t2 -> P (trm_app t1 t2).
  Hypothesis trm_tabs_case : forall (e : trm),
      P e -> P (trm_tabs e).
  Hypothesis trm_tapp_case : forall (e : trm) T,
      P e -> P (trm_tapp e T).
  Hypothesis trm_fix_case : forall (e : trm) T,
      P e -> P (trm_fix T e).
  Hypothesis trm_match_case : forall (clauses : list Clause) (G : GADTName) (e : trm),
      P e ->
      (* (forall TN e', In (clause TN e') ls -> P e') -> *)
      Forall (fun c => P (clauseTerm c)) clauses ->
      P (trm_matchgadt e G clauses).
  Hypothesis trm_let_case : forall (t1 t2 : trm),
      P t1 -> P t2 -> P (trm_let t1 t2).

  Fixpoint trm_ind' (t : trm) : P t :=
    let fix list_clause_ind (clauses : list Clause) : Forall (fun c => P (clauseTerm c)) clauses :=
        match clauses return (Forall (fun c => P (clauseTerm c)) clauses) with
        | nil => Forall_nil (fun c => P (clauseTerm c))
        | cons c rest =>
          let head_proof : P (clauseTerm c) := trm_ind' (clauseTerm c) in
          let tail_proof : Forall (fun c => P (clauseTerm c)) rest := list_clause_ind rest in
          (Forall_cons c head_proof tail_proof)
        end in
    match t with
  | trm_bvar i    => trm_bvar_case i
  | trm_fvar x    => trm_fvar_case x
  | trm_constructor tparams C t => trm_constructor_case tparams C (trm_ind' t)
  | trm_unit => trm_unit_case
  | trm_tuple e1 e2 => trm_tuple_case (trm_ind' e1) (trm_ind' e2)
  | trm_fst e => trm_fst_case (trm_ind' e)
  | trm_snd e => trm_snd_case (trm_ind' e)
  | trm_abs T e => trm_abs_case T (trm_ind' e)
  | trm_app e1 e2 => trm_app_case (trm_ind' e1) (trm_ind' e2)
  | trm_tabs e => trm_tabs_case (trm_ind' e)
  | trm_tapp e T => trm_tapp_case T (trm_ind' e)
  | trm_fix T e => trm_fix_case T (trm_ind' e)
  | trm_matchgadt e G clauses => trm_match_case G (trm_ind' e) (list_clause_ind clauses)
  | trm_let e1 e2 => trm_let_case (trm_ind' e1) (trm_ind' e2)
    end.
End trm_ind'.

(** * Sizes *)

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

Definition map_clause_trms {A : Type} (f : trm -> A) (cs : list Clause) : list A :=
  map (fun c => f (clauseTerm c)) cs.

Definition map_clause_trm_trm (f : trm -> trm) (cs : list Clause) : list Clause :=
  map (fun c => match c with
             | clause n e => clause n (f e)
             end) cs.

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
  | trm_matchgadt e G cs => trm_size e + sum (map_clause_trms trm_size cs)
  | trm_let e1 e2 => 1 + trm_size e1 + trm_size e2
  end.

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
  | trm_matchgadt e1 G cs =>
    (* each clause binds n type variables *)
    trm_matchgadt (open_te_rec k u e1) G
                  (map (fun c => match c with clause n e => clause n (open_te_rec (k + n) u e) end) cs)
  | trm_let e1 e2 => trm_let (open_te_rec k u e1) (open_te_rec k u e2)
  end.

Fixpoint open_ee_rec (k : nat) (u : trm) (e : trm) {struct e} : trm :=
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
  | trm_matchgadt e1 G cs =>
    (* each clause binds 1 value variable *)
    trm_matchgadt (open_ee_rec k u e1) G
                  (map (fun c => match c with clause n e => clause n (open_ee_rec (S k) u e) end) cs)
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

Fixpoint open_te_many (args : list typ) (e : trm) :=
  match args with
  | ha :: ta => open_te_many ta (open_te e ha)
  | [] => e
  end.
(* Fixpoint open_tt_many (args : list typ) (T : typ) : typ := *)
(*   match args with *)
(*   | [] => T *)
(*   | h :: t => open_tt (open_tt_many t T) h *)
(*   end. *)

(* Fixpoint open_te_many (args : list typ) (e : trm) : trm := *)
(*   match args with *)
(*   | [] => e *)
(*   | h :: t => open_te (open_te_many t e) h *)
(*   end. *)

Definition open_tt_many_var (args : list var) (T : typ) := open_tt_many (map typ_fvar args) T.

Definition open_te_many_var (args : list var) (e : trm) := open_te_many (map typ_fvar args) e.

(** * Free Variables *)

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

Fixpoint fv_typs (Ts : list typ) : fset var :=
  match Ts with
  | nil => \{}
  | cons Th Tts => fv_typ Th \u fv_typs Tts
  end.

(* TODO shall we differentiate free type and term variables? *)

Lemma fv_typs_migration : forall Ts Z,
    fv_typs Ts \u Z =
    fold_left (fun fv T => fv \u fv_typ T) Ts Z.
  induction Ts; introv; cbn.
  - rewrite* union_empty_l.
  - rewrite <- IHTs.
    rewrite (union_comm (fv_typ a) (fv_typs Ts)).
    rewrite <- union_assoc.
    rewrite (union_comm (fv_typ a) Z).
    auto.
Qed.

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
  | trm_matchgadt e _ cs =>
    fold_left (fun fv c => fv \u fv_trm (clauseTerm c)) cs (fv_trm e)
  | trm_constructor Ts _ e1 =>
    fold_left (fun fv T => fv \u fv_typ T) Ts (fv_trm e1)
  end.


(** * Closed types and terms; and values *)

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
| term_matchgadt : forall L e1 G ms,
    term e1 ->
    (forall cl, In cl ms ->
           forall Alphas x,
             length Alphas = clauseArity cl ->
             DistinctList Alphas ->
             (forall A, In A Alphas -> A \notin L) ->
             x \notin L ->
             x \notin from_list Alphas ->
           term ((open_te_many_var Alphas (clauseTerm cl)) open_ee_var x)
    ) ->
    term (trm_matchgadt e1 G ms)
with
value : trm -> Prop :=
| value_abs : forall V e1, term (trm_abs V e1) ->
                      value (trm_abs V e1)
| value_tabs : forall e1, term (trm_tabs e1) ->
                     value (trm_tabs e1)
| value_unit : value (trm_unit)
                     (** TODO value_fvar ??? this is problematic as we have x-vars and f-vars, do we need to differentiate them?; it should be carefully analysed how it influences the language design - it seems that it does not change expressivity significantly *)
| value_tuple : forall e1 e2,
    value e1 ->
    value e2 ->
    value (trm_tuple e1 e2)
| value_gadt : forall Tparams Name e1,
    term (trm_constructor Tparams Name e1) ->
    value e1 ->
    value (trm_constructor Tparams Name e1)
.

(** * GADT Environment definition *)
(*


f : T → ∀α. T
f = λx : T. Λα. x - valid but we cannot encode it
but we can do
f' : T → ∀α. Unit → T
f' = λx : T. Λα. λignored: Unit. x

and instead of applying (f x)[U]
we would apply ((f x)[U]) <> to get the result




*)
Record GADTConstructorDef : Set :=
  (* a constructor of type ∀(α...). τ → (β...) T)
     arity specifies how many type parameters (α) there are, they are referred to inside the types by DeBruijn indices
     τ is the type of argument (one arg only, use tuples for more; it can refer to α)
     β are the instantiated type parameters of the returned GADT type (they can refer to α) - βs are represented by rettypes
     T is the base GADT type name that is returned by this constructor, it is not included in the constructor definition as it is implicit from where this definition is
   *)
  mkGADTconstructor {
      Carity : nat;
      Cargtype : typ;
      Crettypes : list typ
    }.

Record GADTDef : Set :=
  mkGADT {
      Tarity : nat;
      Tconstructors : list GADTConstructorDef
    }.

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

(** * Context *)

(* TODO: move bind_typ to separate env Δ *)

Inductive bind : Set :=
| bind_var : typ -> bind.

(* Notation "'withtyp' X" := (X ~ bind_typ) (at level 31, left associativity). *)
Notation "x ~: T" := (x ~ bind_var T) (at level 27, left associativity).

Unset Implicit Arguments.
Definition ctx := env bind.

(** * Substitution *)

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
  | trm_matchgadt e G cs =>
    trm_matchgadt (subst_te Z U e) G (map_clause_trm_trm (subst_te Z U) cs)
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
  | trm_matchgadt e G cs =>
    trm_matchgadt (subst_ee z u e) G (map_clause_trm_trm (subst_ee z u) cs)
  | trm_constructor Ts N e1 => trm_constructor Ts N (subst_ee z u e1)
  end.

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_typ => bind_typ
  (* | bind_var T => bind_var (subst_tt Z P T) *)
  end.

(** * Well-formed types *)
(* (TODO clarify) In pDOT there is no such notion as a type is well formed if it is used in a typing judgement.
But this language requires it, because like in System F we have type-abstractions and type-applications.
In type-application we need a way to ensure that the type is well-formed.
In pDOT type-abstraction is handled by dependent typing and type-application is implemented by applying a term containing a type-member, so we get its well-formedness from the fact that the term containing this type is well-typed.
But in this calculus we apply 'naked' types, so there are no typing judgements for them, so we need a separate notion.
 *)

Definition substitution := list (var * typ).
Definition substitution_sources (Θ : substitution) : fset var := from_list (map fst Θ).

Inductive type_equation : Set := mk_type_equation (T U : typ).

Notation "T ≡ U" := (mk_type_equation T U) (at level 30).

Inductive typctx_elem : Set :=
| tc_var (A : var)
| tc_eq (eq : type_equation).

Coercion typ_fvar : var >-> typ.
Coercion tc_var : var >-> typctx_elem.
Coercion tc_eq : type_equation >-> typctx_elem.

(* we keep the elements in reverse order, i.e. the head is the last added element *)
Definition typctx := list typctx_elem.
Definition is_var_defined (Δ : typctx) (X : var) : Prop := In (tc_var X) Δ.
(* Definition add_var (Δ : typctx) (X : var) : typctx := tc_var X :: Δ. *)
(* Definition add_eq (Δ : typctx) (eq : type_equation) : typctx := tc_eq eq :: Δ. *)
Definition emptyΔ : typctx := [].
Notation "A |,| B" := (A ++ B) (at level 32).

Inductive wft : GADTEnv -> typctx -> typ -> Prop :=
| wft_unit : forall Σ Δ,
    wft Σ Δ typ_unit
| wft_var : forall Σ Δ X,
    is_var_defined Δ X ->
    wft Σ Δ (typ_fvar X)
| wft_arrow : forall Σ Δ T1 T2,
    wft Σ Δ  T1 ->
    wft Σ Δ T2 ->
    wft Σ Δ (typ_arrow T1 T2)
| wft_tuple : forall Σ Δ T1 T2,
    wft Σ Δ T1 ->
    wft Σ Δ T2 ->
    wft Σ Δ (typ_tuple T1 T2)
| wft_all : forall (L : fset var) Σ Δ T2,
    (forall X, X \notin L ->
          wft Σ (Δ |,| [tc_var X]) (T2 open_tt_var X)) ->
    wft Σ Δ (typ_all T2)
| wft_gadt : forall Σ Δ Tparams Name Arity Defs,
    (forall T, In T Tparams -> wft Σ Δ T) ->
    binds Name (mkGADT Arity Defs) Σ ->
    length Tparams = Arity ->
    wft Σ Δ (typ_gadt Tparams Name)
.

Definition alpha_equivalent (T U : typ) : Prop := T = U. (*Thanks to usage of de Bruijn indices, alpha equivalence reduces to plain equivalence *)

Fixpoint subst_tt' (T : typ) (Θ : substitution) :=
  match Θ with
  | nil => T
  | (A, U) :: Θ' => subst_tt' (subst_tt A U T) Θ'
  end.

(* Fixpoint subst_tt' (T : typ) (Θ : substitution) : typ := *)
(*   match T with *)
(*   | typ_bvar J => typ_bvar J *)
(*   (* | typ_fvar X => If X = Z then U else (typ_fvar X) *) *)
(*   | typ_fvar X => If X = Z then U else (typ_fvar X) *)
(*   | typ_unit   => typ_unit *)
(*   | T1 ** T2   => subst_tt Z U T1 ** subst_tt Z U T2 *)
(*   | T1 ==> T2   => subst_tt Z U T1 ==> subst_tt Z U T2 *)
(*   | typ_all T1 => typ_all (subst_tt Z U T1) *)
(*   | typ_gadt Ts Name => typ_gadt (map (subst_tt Z U) Ts) Name *)
(*   end. *)
Inductive subst_matches_typctx Σ : typctx -> substitution -> Prop :=
| tc_empty : subst_matches_typctx Σ [] []
| tc_add_var : forall Θ Δ A T,
    wft Σ Δ T ->
    subst_matches_typctx Σ Δ Θ ->
    subst_matches_typctx Σ (tc_var A :: Δ) ((A, T) :: Θ)
| tc_add_eq : forall Θ Δ T1 T2,
    subst_matches_typctx Σ Δ Θ ->
    alpha_equivalent (subst_tt' T1 Θ) (subst_tt' T2 Θ) ->
    subst_matches_typctx Σ (tc_eq (T1 ≡ T2) :: Δ) Θ.

Definition entails_semantic Σ (Δ : typctx) (eq : type_equation) :=
  match eq with
  | T1 ≡ T2 =>
    forall Θ, subst_matches_typctx Σ Δ Θ ->
         alpha_equivalent (subst_tt' T1 Θ) (subst_tt' T2 Θ)
  end.

(** * Well-formedness of the GADT definitions and the envionment *)

(* Fixpoint add_types (Δ : typctx) (args : list var) := *)
(*   match args with *)
(*   | [] => Δ *)
(*   | Th :: Tts => add_types (Δ |,| [tc_var Th]) Tts *)
(*   end. *)
Definition tc_vars (Xs : list var) : typctx :=
  List.map tc_var Xs.

Inductive okConstructorDef : GADTEnv ->  nat -> GADTConstructorDef -> Prop :=
(* TODO are these conditions enough? *)
| ok_constr_def : forall Tarity Carity argT Σ retTs,
    (* TODO the L may need to be moved inside the Alphas-props *)
    length retTs = Tarity ->
    (forall Alphas L Δ,
        DistinctList Alphas ->
        length Alphas = Carity ->
        (forall alpha, In alpha Alphas -> alpha \notin L) ->
        wft Σ (Δ |,| tc_vars Alphas) (open_tt_many_var Alphas argT)
    ) ->
    (forall Alphas L Δ,
        DistinctList Alphas ->
        length Alphas = Carity ->
        (forall alpha, In alpha Alphas -> alpha \notin L) ->
        (forall retT,
            In retT retTs ->
            wft Σ (Δ |,| tc_vars Alphas) (open_tt_many_var Alphas retT))
    ) ->
    fv_typ argT = \{} ->
    (forall rT, List.In rT retTs -> fv_typ rT = \{}) -> (* the types have no free variables, but can of course reference other GADTs since these are not counted as free vars *)
    (* this is a peculiar situation because normally the de bruijn type vars would be bound to a forall, but here we can't do that directly, we don't want to use free variables either, maybe a separate well formed with N free type vars judgement will help? *)
    okConstructorDef Σ Tarity (mkGADTconstructor Carity argT retTs).

Definition okGadt (Σ : GADTEnv) : Prop :=
  ok Σ /\
  forall Name Arity Defs,
    binds Name (mkGADT Arity Defs) Σ ->
    Defs <> [] /\
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

(* This seems to not be enforced in the paper, at least explicitly, and indeed maybe it is not necessary - in practice we will only add wft types, but for the equations that does not seem to matter *)
(* Definition oktypctx (Σ : GADTEnv) (Δ : typctx) : Prop := *)
(*   (forall T1 T2, (T1 ≡ T2) \in (Δeqs Δ) -> wft Σ Δ T1 /\ wft Σ Δ T2). *)

Inductive okt : GADTEnv -> typctx -> ctx -> Prop :=
| okt_empty : forall Σ Δ,
    okGadt Σ ->
    (* oktypctx Σ Δ -> *)
    okt Σ Δ empty
| okt_typ : forall Σ Δ E x T,
    okt Σ Δ E -> wft Σ Δ T -> x # E -> okt Σ Δ (E & x ~: T).

(** * Typing *)

Reserved Notation "{ Σ , Δ ,  E }  ⊢ t ∈ T" (at level 0, Σ at level 99, T at level 69).

Inductive typing : GADTEnv -> typctx -> ctx -> trm -> typ -> Prop :=
  (* TODO typing_eq *)
| typing_unit : forall Σ Δ E,
    okt Σ Δ E ->
    {Σ, Δ, E} ⊢ trm_unit ∈ typ_unit
| typing_var : forall Σ E Δ x T,
    binds x (bind_var T) E ->
    okt Σ Δ E ->
    {Σ, Δ, E} ⊢ (trm_fvar x) ∈ T
| typing_cons : forall Σ E Δ Ts Name Ctor e1 Tarity Ctors Carity CargType CretTypes Targ Tret,
    {Σ, Δ, E} ⊢ e1 ∈ Targ ->
    binds Name (mkGADT Tarity Ctors) Σ ->
    nth_error Ctors Ctor = Some (mkGADTconstructor Carity CargType CretTypes) ->
    length Ts = Carity ->
    Targ = open_tt_many Ts CargType ->
    (forall T, In T Ts -> wft Σ Δ T) ->
    (* alternatively: Tret = open_tt_many (typ_gadt (List.map (fun T => open_tt_many T Ts) CretTypes) Name) Ts -> *)
    Tret = open_tt_many Ts (typ_gadt CretTypes Name) ->
    {Σ, Δ, E} ⊢ trm_constructor Ts (Name, Ctor) e1 ∈ Tret
| typing_abs : forall L Σ Δ E V e1 T1,
    (forall x, x \notin L -> {Σ, Δ, E & x ~: V} ⊢ e1 open_ee_var x ∈ T1) ->
    {Σ, Δ, E} ⊢ trm_abs V e1 ∈ V ==> T1
| typing_app : forall Σ Δ E T1 T2 e1 e2,
    {Σ, Δ, E} ⊢ e2 ∈ T1 ->
    {Σ, Δ, E} ⊢ e1 ∈ T1 ==> T2 ->
    {Σ, Δ, E} ⊢ trm_app e1 e2 ∈ T2
| typing_tabs : forall L Σ Δ E e1 T1,
    (forall X, X \notin L -> (* TODO consider splitting value and term as this case may be problematic ? *)
          value (e1 open_te_var X)) ->
    (forall X, X \notin L ->
          {Σ, Δ |,| [tc_var X], E} ⊢ (e1 open_te_var X) ∈ (T1 open_tt_var X)) ->
    {Σ, Δ, E} ⊢ (trm_tabs e1) ∈ typ_all T1
| typing_tapp : forall Σ Δ E e1 T1 T T',
    {Σ, Δ, E} ⊢ e1 ∈ typ_all T1 ->
    wft Σ Δ T ->
    T' = open_tt T1 T ->
    {Σ, Δ, E} ⊢ trm_tapp e1 T ∈ T'
| typing_tuple : forall Σ Δ E T1 T2 e1 e2,
    {Σ, Δ, E} ⊢ e1 ∈ T1 ->
    {Σ, Δ, E} ⊢ e2 ∈ T2 ->
    {Σ, Δ, E} ⊢ trm_tuple e1 e2 ∈ T1 ** T2
| typing_fst : forall Σ Δ E T1 T2 e1,
    {Σ, Δ, E} ⊢ e1 ∈ T1 ** T2 ->
    {Σ, Δ, E} ⊢ trm_fst e1 ∈ T1
| typing_snd : forall Σ Δ E T1 T2 e1,
    {Σ, Δ, E} ⊢ e1 ∈ T1 ** T2 ->
    {Σ, Δ, E} ⊢ trm_snd e1 ∈ T2
| typing_fix : forall L Σ Δ E T v,
    (forall x, x \notin L -> value (v open_ee_var x)) ->
    (forall x, x \notin L -> {Σ, Δ, E & x ~: T} ⊢ (v open_ee_var x) ∈ T) ->
    {Σ, Δ, E} ⊢ trm_fix T v ∈ T
| typing_let : forall L Σ Δ E V T2 e1 e2,
    {Σ, Δ, E} ⊢ e1 ∈ V ->
    (forall x, x \notin L -> {Σ, Δ, E & x ~: V} ⊢ e2 open_ee_var x ∈ T2) ->
    {Σ, Δ, E} ⊢ trm_let e1 e2 ∈ T2
(* typing case merges rules ty-case and pat-cons from the original paper *)
| typing_case : forall L Σ Δ E e ms Ts T Name Tc Tarity Defs,
    {Σ, Δ, E} ⊢ e ∈ T ->
    T = (typ_gadt Ts Name) ->
    binds Name (mkGADT Tarity Defs) Σ ->
    length Defs = length ms -> (* implicit exhaustivity check *)
    (* we use zip instead of Forall2 to get better induction for free, but can rephrase it as needed using equivalence thm  *)
    (forall def clause, In (def, clause) (zip Defs ms) ->
                   (* this is because in pat-cons alphas of same length is in c[...] (clauseArity) and forall ... (def Carity) *)
                   clauseArity clause = Carity def) ->
    (forall def clause, In (def, clause) (zip Defs ms) ->
               forall Alphas x,
                 length Alphas = Carity def ->
                 DistinctList Alphas -> (* not sure if this is necessary, but may be helpful*)
                 (forall A, In A Alphas -> A \notin L) ->
                 x \notin L ->
                 x \notin from_list Alphas -> (* Alphas are distinct but also x is not part of them *)
                 (* TODO for now we do not have add the type equalities, without them the existential tpes are mostly useless; will be added in next iteration
                    TODO add to judgement type equality of (open_tt_many_var Alphas Crettypes) == Ts
                  *)
                 { Σ,
                   (Δ |,| tc_vars Alphas),
                   E
                   & x ~: (open_tt_many_var Alphas (Cargtype def))
                 } ⊢ (open_te_many_var Alphas (clauseTerm clause)) open_ee_var x ∈ Tc
            ) ->
    { Σ, Δ, E } ⊢ trm_matchgadt e Name ms ∈ Tc
where "{ Σ , Δ , E } ⊢ t ∈ T" := (typing Σ Δ E t T).

(** * Reduction rules (Small-step operational semantics) *)

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
| red_match : forall e1 G cid Ts ms Carity Ce e',
    value (trm_constructor Ts (G, cid) e1) ->
    nth_error ms cid = Some (clause Carity Ce) ->
    length Ts = Carity -> (* do we need this additional assumption? seems to be derivable from typing, but maybe better keep it for sanity *)
    e' = open_ee (open_te_many Ts Ce) e1 ->
    trm_matchgadt (trm_constructor Ts (G, cid) e1) G ms --> e'
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
| ered_match : forall e1 G ms e1',
    e1 --> e1' ->
    trm_matchgadt e1 G ms --> trm_matchgadt e1' G ms
where "e1 --> e2" := (red e1 e2).

(** * Statemenf of desired safety properties *)

Definition progress := forall Σ e T,
    {Σ, emptyΔ, empty} ⊢ e ∈ T ->
    (value e) \/ (exists e', e --> e').

Definition preservation := forall Σ e T e',
    {Σ, emptyΔ, empty} ⊢ e ∈ T ->
    e --> e' ->
    {Σ, emptyΔ, empty} ⊢ e' ∈ T.
