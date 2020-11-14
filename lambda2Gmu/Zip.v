Set Implicit Arguments.
Require Import List.
Require Import TLC.LibTactics.
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

  Lemma F2_from_zip : forall la lb,
      length la = length lb ->
      (forall a b, In (a,b) (zip la lb) -> R a b) ->
      Forall2 R la lb.
    intros.
    apply F2_iff_In_zip.
    eauto.
  Qed.

End Zip.

Ltac listin :=
  match goal with
  | |- List.In ?e (?h :: ?t) =>
    cbn; solve [right* | left*]
  end.

Hint Extern 4 (List.In _ (_ :: _)) => (cbn; solve [left* | right*]) : listin.

Lemma forall2_from_snd : forall T1 T2 (P : T1 -> T2 -> Prop) (As : list T1) (Bs : list T2) (B : T2),
    List.Forall2 P As Bs ->
    List.In B Bs ->
    exists A, (List.In A As /\ List.In (A,B) (zip As Bs) /\ P A B).
  induction 1.
  - intros. contradiction.
  - introv Bin.
    inversions Bin.
    + exists x. splits*.
      * eauto with listin.
      * constructor*.
    + lets [A [InA PA]]: IHForall2 H1.
      exists A. splits*.
      * eauto with listin.
      * cbn. right*.
Qed.

Lemma forall2_from_snd_zip : forall T1 T2 (P : T1 -> T2 -> Prop) (As : list T1) (Bs : list T2) (B : T2),
    length As = length Bs ->
    (forall a b, In (a,b) (zip As Bs) -> P a b) ->
    List.In B Bs ->
    exists A, (List.In A As /\ List.In (A,B) (zip As Bs) /\ P A B).
  intros.
  eapply forall2_from_snd; eauto.
  apply F2_iff_In_zip. eauto.
Qed.
