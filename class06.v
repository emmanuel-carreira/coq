(** **** Exercise: (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

(** **** Exercise: (list_funs)  *)
(** Complete as definições de [nonzeros],
    [oddmembers] e [countoddmembers]. Os testes
    mostram o comportamento esperado. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if beq_nat h 0
              then nonzeros t
              else h :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. 
  simpl. reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if Nat.odd h
              then h :: (oddmembers t)
              else oddmembers t
end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  simpl. reflexivity.
Qed.

Definition countoddmembers (l:natlist) : nat :=
  match l with
  | nil => 0
  | _ => length (oddmembers l)
end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  simpl. reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
  simpl. reflexivity.
Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
  simpl. reflexivity.
Qed.