Require GMu.Definitions.
Require GMuAnnot.Definitions.
Require Definitions.
Require Reduction.
Require Sequences.
Require Import TLC.LibEnv.

Module Source.
  Import GMu.Definitions.
  Include GMu.Definitions.
End Source.

Module SourceAnnot.
  Import GMuAnnot.Definitions.
  Include GMuAnnot.Definitions.
End SourceAnnot.

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