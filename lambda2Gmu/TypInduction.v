Require Import Definitions.
Require Import Zip.
Require Import TLC.LibLN.
Require Import List.
Import List.ListNotations.

Lemma typing_ind_ext
     : forall P : typing_taint -> GADTEnv -> typctx -> ctx -> trm -> typ -> Prop,
       (forall (Σ : GADTEnv) (Δ : typctx) (E : ctx),
        okt Σ Δ E -> P Treg Σ Δ E trm_unit typ_unit) ->
       (forall (Σ : GADTEnv) (E : env bind) (Δ : typctx) (x : var) (T : typ),
        binds x (bind_var T) E -> okt Σ Δ E -> P Treg Σ Δ E (trm_fvar x) T) ->
       (forall (Σ : GADTEnv) (E : ctx) (Δ : typctx) (TT1 : typing_taint)
          (Ts : list typ) (Name : var) (Ctor : nat) (e1 : trm) 
          (Tarity : nat) (Ctors : list GADTConstructorDef) 
          (Carity : nat) (CargType : typ) (CretTypes : list typ) 
          (Targ Tret : typ),
        {Σ, Δ, E} ⊢( TT1) e1 ∈ Targ ->
        P TT1 Σ Δ E e1 Targ ->
        binds Name {| Tarity := Tarity; Tconstructors := Ctors |} Σ ->
        nth_error Ctors Ctor =
        Some {| Carity := Carity; Cargtype := CargType; Crettypes := CretTypes |} ->
        length Ts = Carity ->
        Targ = open_tt_many Ts CargType ->
        (forall T : typ, In T Ts -> wft Σ Δ T) ->
        Tret = open_tt_many Ts (typ_gadt CretTypes Name) ->
        P Treg Σ Δ E (trm_constructor Ts (Name, Ctor) e1) Tret) ->
       (forall (L : fset var) (Σ : GADTEnv) (Δ : typctx) (E : env bind) 
          (V : typ) (e1 : trm) (T1 : typ) (TT : typing_taint),
        (forall x : var, x \notin L -> {Σ, Δ, E & x ~: V} ⊢( TT) e1 open_ee_var x ∈ T1) ->
        (forall x : var, x \notin L -> P TT Σ Δ (E & x ~: V) (e1 open_ee_var x) T1) ->
        P Treg Σ Δ E (trm_abs V e1) (V ==> T1)) ->
       (forall (Σ : GADTEnv) (Δ : typctx) (E : ctx) (T1 T2 : typ) 
          (e1 e2 : trm) (TT1 TT2 : typing_taint),
        {Σ, Δ, E} ⊢( TT1) e2 ∈ T1 ->
        P TT1 Σ Δ E e2 T1 ->
        {Σ, Δ, E} ⊢( TT2) e1 ∈ T1 ==> T2 ->
        P TT2 Σ Δ E e1 (T1 ==> T2) -> P Treg Σ Δ E (trm_app e1 e2) T2) ->
       (forall (L : fset var) (Σ : GADTEnv) (Δ : list typctx_elem) 
          (E : ctx) (e1 : trm) (T1 : typ) (TT : typing_taint),
        (forall X : var, X \notin L -> value (e1 open_te_var X)) ->
        (forall X : var,
         X \notin L ->
         {Σ, Δ |,| [tc_var X], E} ⊢( TT) e1 open_te_var X ∈ T1 open_tt_var X) ->
        (forall X : var,
         X \notin L ->
         P TT Σ (Δ |,| [tc_var X]) E (e1 open_te_var X) (T1 open_tt_var X)) ->
        P Treg Σ Δ E (trm_tabs e1) (typ_all T1)) ->
       (forall (Σ : GADTEnv) (Δ : typctx) (E : ctx) (e1 : trm) 
          (T1 T T' : typ) (TT : typing_taint),
        {Σ, Δ, E} ⊢( TT) e1 ∈ typ_all T1 ->
        P TT Σ Δ E e1 (typ_all T1) ->
        wft Σ Δ T -> T' = open_tt T1 T -> P Treg Σ Δ E (trm_tapp e1 T) T') ->
       (forall (Σ : GADTEnv) (Δ : typctx) (E : ctx) (T1 T2 : typ) 
          (e1 e2 : trm) (TT1 TT2 : typing_taint),
        {Σ, Δ, E} ⊢( TT1) e1 ∈ T1 ->
        P TT1 Σ Δ E e1 T1 ->
        {Σ, Δ, E} ⊢( TT2) e2 ∈ T2 ->
        P TT2 Σ Δ E e2 T2 -> P Treg Σ Δ E (trm_tuple e1 e2) (T1 ** T2)) ->
       (forall (Σ : GADTEnv) (Δ : typctx) (E : ctx) (T1 T2 : typ) 
          (e1 : trm) (TT : typing_taint),
        {Σ, Δ, E} ⊢( TT) e1 ∈ T1 ** T2 ->
        P TT Σ Δ E e1 (T1 ** T2) -> P Treg Σ Δ E (trm_fst e1) T1) ->
       (forall (Σ : GADTEnv) (Δ : typctx) (E : ctx) (T1 T2 : typ) 
          (e1 : trm) (TT : typing_taint),
        {Σ, Δ, E} ⊢( TT) e1 ∈ T1 ** T2 ->
        P TT Σ Δ E e1 (T1 ** T2) -> P Treg Σ Δ E (trm_snd e1) T2) ->
       (forall (L : fset var) (Σ : GADTEnv) (Δ : typctx) (E : env bind) 
          (T : typ) (v : trm) (TT : typing_taint),
        (forall x : var, x \notin L -> value (v open_ee_var x)) ->
        (forall x : var, x \notin L -> {Σ, Δ, E & x ~: T} ⊢( TT) v open_ee_var x ∈ T) ->
        (forall x : var, x \notin L -> P TT Σ Δ (E & x ~: T) (v open_ee_var x) T) ->
        P Treg Σ Δ E (trm_fix T v) T) ->
       (forall (L : fset var) (Σ : GADTEnv) (Δ : typctx) (E : ctx) 
          (V T2 : typ) (e1 e2 : trm) (TT1 TT2 : typing_taint),
        {Σ, Δ, E} ⊢( TT1) e1 ∈ V ->
        P TT1 Σ Δ E e1 V ->
        (forall x : var, x \notin L -> {Σ, Δ, E & x ~: V} ⊢( TT2) e2 open_ee_var x ∈ T2) ->
        (forall x : var, x \notin L -> P TT2 Σ Δ (E & x ~: V) (e2 open_ee_var x) T2) ->
        P Treg Σ Δ E (trm_let e1 e2) T2) ->
       (forall (L : fset var) (Σ : GADTEnv) (Δ : typctx) (E : ctx) 
          (e : trm) (ms : list Clause) (Ts : list typ) (T : typ) 
          (Name : GADTName) (Tc : typ) (Tarity : nat) (Defs : list GADTConstructorDef)
          (TT1 : typing_taint),
        {Σ, Δ, E} ⊢( TT1) e ∈ T ->
        P TT1 Σ Δ E e T ->
        T = typ_gadt Ts Name ->
        binds Name {| Tarity := Tarity; Tconstructors := Defs |} Σ ->
        length Defs = length ms ->
        (forall (def : GADTConstructorDef) (clause : Clause),
         In (def, clause) (zip Defs ms) -> clauseArity clause = Carity def) ->
        (forall (def : GADTConstructorDef) (clause : Clause),
         In (def, clause) (zip Defs ms) ->
         exists TTc : typing_taint,
           forall (Alphas : list var) (x : var),
           length Alphas = Carity def ->
           DistinctList Alphas ->
           (forall A : var, In A Alphas -> A \notin L) ->
           x \notin L ->
           x \notin from_list Alphas ->
           ({Σ, (Δ |,| tc_vars Alphas) |,| equations_from_lists Ts (Crettypes def),
           E & x ~: open_tt_many_var Alphas (Cargtype def)}
             ⊢( TTc) open_te_many_var Alphas (clauseTerm clause) open_ee_var x ∈ Tc)
           /\ (P TTc Σ
                ((Δ |,| tc_vars Alphas) |,| equations_from_lists Ts (Crettypes def))
                (E & x ~: open_tt_many_var Alphas (Cargtype def))
                (open_te_many_var Alphas (clauseTerm clause) open_ee_var x)
                Tc)
        ) ->
        P Treg Σ Δ E (trm_matchgadt e Name ms) Tc) ->
       (forall (Σ : GADTEnv) (Δ : typctx) (E : ctx) (T1 T2 : typ) 
          (e : trm) (TT : typing_taint),
        {Σ, Δ, E} ⊢( TT) e ∈ T1 ->
        P TT Σ Δ E e T1 -> entails_semantic Σ Δ (T1 ≡ T2) -> P Tgen Σ Δ E e T2) ->
       forall (t : typing_taint) (g : GADTEnv) (t0 : typctx) 
         (c : ctx) (t1 : trm) (t2 : typ), {g, t0, c} ⊢( t) t1 ∈ t2 -> P t g t0 c t1 t2.
  intros P Iunit Ifvar Ictor
         Iabs Iapp Iall Itapp Ituple Ifst Isnd Ifix Ilet Imatch Ieq.
  refine (fix F (t : typing_taint) (g : GADTEnv) (t0 : typctx) (c : ctx) (t1 : trm) (t2 : typ) (Typing : {g, t0, c} ⊢( t) t1 ∈ t2) {struct Typing} : P t g t0 c t1 t2 := _).
  destruct Typing; eauto.
  - eapply Imatch; eauto.
    intros.
    lets [TTc IH]: H3 H4.
    exists TTc.
    eauto.
Qed.
