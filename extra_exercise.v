Inductive btree (X : Type) : Type :=
  | bnil : btree X
  | node : X -> btree X -> btree X -> btree X.

Arguments bnil {X}.
Arguments node {X}.

Definition is_empty {X : Type} (b : btree X) : bool :=
  match b with
  | bnil => true
  | _ => false
end.

Example is_empty_test1 :
  forall (X : Type), is_empty (@bnil X) = true.
Proof. reflexivity. Qed.

Example is_empty_test2 :
  is_empty (node 2 bnil bnil) = false.
Proof. reflexivity. Qed.

Fixpoint count {X : Type} (b : btree X) : nat :=
  match b with
  | bnil => 0
  | node _ l r => 1 + count l + count r
end.


Example count_test1 :
  forall (X : Type), count (@bnil X) = 0.
Proof. reflexivity. Qed.

Example count_test2 :
  count (node 2 bnil bnil) = 1.
Proof. reflexivity. Qed.

(* Usando função less than (estritamente menor) que não foi implementada; insert e find são funções de alta ordem*)

Fixpoint insert {X : Type} (x : X) (b : btree X)
                (lt : X -> X -> bool) : btree X:=
  match b with
  | bnil => node x bnil bnil
  | node v l r => if lt x v 
                  then node v (insert x l lt) r
                  else if lt v x
                       then node v l (insert x r lt)
                       else b
end.

Fixpoint find {X : Type} (x : X) (b : btree X)
                (lt : X -> X -> bool) : bool:=
  match b with
  | bnil => false
  | node v l r => if lt x v 
                  then find x l lt
                  else if lt v x
                       then find x r
                       else true
end.
