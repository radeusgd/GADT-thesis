Require GMu.Definitions.
Require Definitions.
Require Reduction.
Require Sequences.
Require Import TLC.LibEnv.

Module Source.
  Import GMu.Definitions.
  Include GMu.Definitions.
End Source.

Module Target.
  Import Definitions.
  Include Definitions.
  Import Reduction.
  Include Reduction.
  Import Sequences.
  Include Sequences.
End Target.

Inductive typed_target_term : Set :=
  typed_target_term_cons : forall (t : Target.trm) (T : Target.typ) (Htyp : Target.ty_trm empty t T), typed_target_term.

Definition get_term (R : typed_target_term) : Target.trm :=
  match R with
  | typed_target_term_cons t _ _ => t
  end.

(*
The translation function is supposed to take a source typing derivation and return a typing derivation of analogous term in the target language. Thus, such a definition is also a proof of typing-preservation of the translation.
*)
(* Definition translation_type := *)
(*   forall (Σ : Source.GADTEnv) *)
(*     (t : Source.trm) (T : Source.typ) *)
(*     (Henv : Source.okGadt Σ) *)
(*     (Htyp : Source.typing Σ empty t T), *)
(*     exists pTT : typed_target_term,  . *)


(* TODO: we will probably decouple translation of Source.GADTEnv from translation of terms, we may also decouple them in this definition ? *)

(* Section translation_semantics. *)
(*   Variable translator : translation_type. *)

(*   Definition target_evaluates := Target.star Target.red. *)
(*   (* This may likely change. *)
(*   The initial idea is to say that for every reduction in the source calculus, we can find an analogous series of reductions in the target *) *)
(*   Definition translation_preserves_semantics := *)
(*     forall (Σ : Source.GADTEnv) *)
(*       (ts : Source.trm) (Ts : Source.typ) *)
(*       (ts' : Source.trm) *)
(*       (Henv : Source.okGadt Σ) *)
(*       (Htyp : Source.typing Σ empty ts Ts) *)
(*       (R : typed_target_term) *)
(*       (Htranslates : translator Σ ts Ts Henv Htyp = R) *)
(*       (Htyp' : Source.typing Σ empty ts' Ts) *)
(*       (HsrcRed : Source.red ts ts'), *)
(*     exists (γ γ' : Target.sta) (* TODO handling the stores, may have to happen inside translation???? *) *)
(*       (R' : typed_target_term), *)
(*       translator Σ ts' Ts Henv Htyp' = R' /\ *)
(*       target_evaluates (γ, get_term R) (γ', get_term R'). *)

(*   (* another approach could be to characterize just the looping or final values *) *)
(*   (* something like: *)
(*      forall ts, *)
(*             ts loops -> (translate ts) loops *)
(*          /\ ts endswithval v -> (translate ts) ends with val v' /\ (translateVal v = v') *)
(*   *) *)

(* End translation_semantics. *)
