(** **** Exercise: (ev_double)  *)
Theorem ev_double :
  forall n, ev (double n).
Proof.
  intros. induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

(** **** Exercise: (SSSSev__even)  *)
(** Prove o seguinte resultado usando [inversion]. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.

(** **** Exercise: (even5_nonsense)  *)
(** Prove o seguinte resultado usando [inversion]. *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3.
Qed.