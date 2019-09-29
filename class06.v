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

(** **** Exercise: (bag_functions)  *)
(** Complete as definições de: [count], [sum],
    [add], e [member] para multiconjuntos (bags).
    Os testes mostram o comportamento esperado. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => if beq_nat v h
              then S (count v t)
              else (count v t)
end.

Example test_count1:
  count 1 [1;2;3;1;4;1] = 3.
Proof.
  simpl. reflexivity.
Qed.

Example test_count2:
  count 6 [1;2;3;1;4;1] = 0.
Proof.
  simpl. reflexivity.
Qed.

Definition sum : bag -> bag -> bag := app.
  

Example test_sum1:
  count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
  simpl. reflexivity.
Qed.

Definition add (v:nat) (s:bag) : bag := app s [v].

Example test_add1:
  count 1 (add 1 [1;4;1]) = 3.
Proof.
  simpl. reflexivity.
Qed.

Example test_add2:
  count 5 (add 1 [1;4;1]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Definition member (v:nat) (s:bag) : bool := negb (beq_nat (count v s)  0).

Example test_member1:
  member 1 [1;4;1] = true.
Proof.
  reflexivity.
Qed.

Example test_member2:
  member 2 [1;4;1] = false.
Proof.
  reflexivity.
Qed.

(** **** Exercise: (bag_theorem)  *)
(** Prove o seguinte teorema. Talvez você
    precise provar um teorema auxiliar. *)

Theorem bag_theorem :
  forall (v : nat) (b : bag),
    (count v (add v b)) = (1 + (count v b)).
Proof.
  intros. destruct add. Abort.

(** **** Exercise: (list_exercises)  *)
(** Prove os seguintes teoremas. *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - induction l2.
    + simpl. reflexivity.
    + simpl. rewrite app_nil_r. reflexivity. 
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros. induction l1.
  - reflexivity.
  - 
Abort.

(** **** Exercise: (beq_natlist)  *)
(** Complete a definição de [beq_natlist], que
    compara listas de números. Veja os exemplos.
    Em seguida, prove o teorema [beq_natlist_refl]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _ , [] => false
  | h1 :: t1, h2 :: t2 => if beq_nat h1 h2
                         then beq_natlist t1 t2
                         else false
end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof.
  reflexivity.
Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof.
  reflexivity.
Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof.
  reflexivity.
Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [| n l].
  - reflexivity.
  - rewrite IHl. simpl.
Abort.