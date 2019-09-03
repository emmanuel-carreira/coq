Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | []      => ([], [])
  | (x,y) :: l' => (x :: fst (split l'), y :: snd (split l'))
  end.

Definition hd_error {X : Type} (l : list X)
           : option X:=
  match l with
  | [] => None
  | h :: tl => Some h
end.