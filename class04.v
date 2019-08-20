(*Inductive btree : Type :=
  | leaf : btree
  | node : nat -> btree -> leaf -> leaf.

Check leaf.

*)

Theorem comm_add : forall n m : nat, n + m = m + n.
Proof. Admitted.


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

(* Se não for usar hipótese indutiva, não usar inductive, usar destruct *)

(** **** Exercise: (zero_nbeq_plus_1)  *)
(** Prova a seguinte afirmação usando [destruct] *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* COMPLETE AQUI *) 
  intros. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

(** **** Exercise: (andb_true_elim2)  *)
(** Prova a seguinte afirmação usando [destruct] *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* COMPLETE AQUI *) 
  intros b c. destruct b, c.
  - simpl. intro. reflexivity.
  - simpl. intro. rewrite H. reflexivity.
  - simpl. intro. inversion H.
  - simpl. intro. rewrite H. reflexivity.
Qed.