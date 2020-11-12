Require Import List.
Open Scope list_scope.

Section Zip.
  Variables A B:Type.
  Variable R : A -> B -> Prop.

  Fixpoint zip la lb : list (A * B) :=
  match la,lb with
  | a::lla, b::llb => (a,b) :: zip lla llb
  | _, _ => nil
  end.

  Lemma F2_iff_In_zip : forall la lb,
    Forall2 R la lb <-> (length la = length lb /\ forall a b, In (a,b) (zip la lb) -> R a b).
  Proof.
    intros la lb.
    constructor.
    - generalize la lb.
      induction 1; simpl; intuition; congruence.
    - generalize la lb.
      induction la0; intros lb0 [Hlen HzipR].
      + destruct lb0.
        * econstructor.
        * cbn in Hlen. congruence.
      + destruct lb0.
        * cbn in Hlen. congruence.
        * econstructor.
          -- apply HzipR. econstructor. eauto.
          -- apply IHla0.
             split.
             ++ cbn in Hlen. congruence.
             ++ intros.
                apply HzipR.
                cbn. eauto.
  Qed.

End Zip.
