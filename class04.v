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
