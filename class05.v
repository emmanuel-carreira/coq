(** **** Exercise: (basic_induction)  *)
(** Prove os seguintes teoremas. Será necessário
    buscar por resultados previamente provados. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros. Print Nat.add. induction n.
  - Print Nat.add. simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros. induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

(** **** Exercise: (mult_comm)  *)
(** Use [assert] para ajudar na prova. Não é
    necessário usar indução. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  Print plus_assoc. rewrite plus_assoc. rewrite plus_assoc.
  assert(H: n + m = m + n).
  { rewrite plus_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* COMPLETE AQUI *) 
  intros. induction m.
  - induction n.
    + reflexivity.
    + Search (0*_). rewrite mult_0_l. Search "mult". rewrite mult_0_r. reflexivity.
  - induction n.
    + Search "mult". rewrite mult_0_r. rewrite mult_0_l. reflexivity.
    + simpl. rewrite <- IHn.
Admitted.