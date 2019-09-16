(*Inductive btree : Type :=
  | leaf : btree
  | node : nat -> btree -> leaf -> leaf.

Check leaf.

*)

(** **** Exercise: (plus_id_exercise)  *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros G.
  rewrite -> H.
  rewrite <- G.
  reflexivity.
Qed.

(** **** Exercise: (mult_S_1)  *)
(** Prove o seguinte teorema usando [rewrite] *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite plus_1_l.
  rewrite H.
  reflexivity.
Qed.

(** **** Exercise: (andb_true_elim2)  *)
(** Prova a seguinte afirmação usando [destruct] *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b, c.
  - simpl. intro. reflexivity.
  - simpl. intro. rewrite H. reflexivity.
  - simpl. intro. inversion H.
  - simpl. intro. rewrite H. reflexivity.
Qed.

(** **** Exercise: (zero_nbeq_plus_1)  *)
(** Prova a seguinte afirmação usando [destruct] *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

