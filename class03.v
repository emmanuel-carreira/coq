(** **** Exercise: 1(factorial)  *)
(** Defina a função fatorial em Coq
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)
                        (if n>0) *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
end.

Example test_factorial1:
(factorial 3) = 6.
Proof. simpl. reflexivity. Qed.


Example test_factorial2:
(factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (blt_nat)  *)
(** A função [blt_nat] testa se um número é
    menor do que outro. Observe que a próxima
    definição não é recursiva. É preciso definir
    [blt_nat] a partir de definições passadas *)

Definition blt_nat (n m : nat) : bool := andb (negb (beq_nat n m)) (leb n m).

Example test_blt_nat1:
(blt_nat 2 2) = false.
Proof. reflexivity. Qed.

Example test_blt_nat2:
(blt_nat 2 4) = true.
Proof. reflexivity. Qed.

Example test_blt_nat3:
(blt_nat 4 2) = false.
Proof. reflexivity. Qed.