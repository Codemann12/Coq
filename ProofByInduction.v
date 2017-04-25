Require Export Basics.


Theorem plus_n_O: forall n :nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.
      
Theorem minus_diag: forall n ,
   minus n n = 0.
Proof.
   intros n. induction n as [| n' IHn'].
 reflexivity. rewrite <- IHn'. reflexivity. Qed.

(* Exercise: 2 stars, recommended (basic_induction)*)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Compute (mult 5 7).
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  reflexivity.  rewrite <- IHn'. Admitted.