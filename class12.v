(** **** Exercise: (not_even_auto)  *)
(** Automatize a prova do seguinte teorema.
    Dica: faça uso de inversion, subst,
          clear, rename, ; e repeat. *)
Theorem not_even_auto : ~ ev 101.
Proof.
  unfold not. intros.
  repeat (inversion H ; clear H ; subst; rename H1 into H. subst.)
Qed.

(** **** Exercise: (or_distributes_over_and)  *)
(** Reescreva a prova de [or_distributes_over_and]
    usando táticas de automação. *)
Theorem or_distributes_over_and' : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  tauto.
Qed.