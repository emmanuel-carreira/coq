(** **** Exercise: (not_implies_our_not)  *)
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P H Q J. unfold not in H. apply H in J. inversion J.
Qed.

(** **** Exercise: (contrapositive)  *)
Theorem contrapositive :
  forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not in H0. unfold not. intros. 
  apply H in H1. apply H0 in H1. apply H1.
Qed.

(** **** Exercise: (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros H. destruct H as [H1 H2].
  apply H2 in H1. inversion H1.
Qed.

(** **** Exercise: (iff_properties)  *)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros. split.
  - intros. apply H.
  - intros. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  unfold iff. intros P Q R H1 H2.
  destruct H1 as [H1A H1B].
  destruct H2 as [H2A H2B].
  split.
  - intros. apply H2A. apply H1A. apply H.
  - intros. apply H1B. apply H2B. apply H.
Qed.

  (** intros. unfold iff in H. destruct H as [H1 H2].
  unfold iff in H0. destruct H0 as [H3 H4]. split.
  - intros. apply H1 in H. apply H3 in H. apply H.
  - intros. Abort.
Qed.*)

(** **** Exercise: (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  unfold iff. intros. split.
  - intros. split.
    + destruct H.
      * left. apply H.
      * destruct H as [H1 H2]. right. apply H1.
    + destruct H.
      * left. apply H.
      * destruct H as [H1 H2]. right. apply H2.
  - intros. destruct H as [H1 H2].
    destruct H1, H2.
    + left. apply H.
    + left. apply H.
    + left. apply H0.
    + right. split.
      * apply H.
      * apply H0.
Qed.