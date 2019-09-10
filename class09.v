(** **** Exercise: (apply_exercise1)  *)
(** Antes, prove os seguintes resultados auxiliares. *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1.  rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IHl. reflexivity.
Qed.


Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' -> l' = rev l.
Proof.
  intros. rewrite H. rewrite rev_involutive. reflexivity.
Qed.

(** **** Exercise: (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros. apply trans_eq with (m:=m). apply H0. apply H.
Qed.