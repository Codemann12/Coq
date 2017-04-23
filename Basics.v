Inductive day: Type :=
   | monday:day
   | tuesday: day
   | wednesday: day
   | Thursday : day
   | friday:day
   | saturday:day
   | sunday: day.


Definition next_day(d:day): day:=
   match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => Thursday
    | Thursday => friday
    | friday => saturday
    | saturday => sunday
    | sunday => monday
    end.

Compute (next_day friday).

Example example: next_day monday = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool: Type :=
   | true : bool
   | false : bool.

(* Exercise: 1 star (nandb) *)


Definition negb(b:bool):bool :=
      match b with
        | true => false
        | false => true
        end.

Definition nandb (b1:bool) (b2:bool) : bool :=
    match b1 with
     | false => true
     | true => negb b2
     end.
 
Compute (nandb true true).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


(* Exercise: 1 star (andb3) *)

Definition andb2 (b1:bool) (b2:bool):bool :=
     match b1 with
       | true  => b2
       | false => false
       
       end.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool:=
     match b1 with
       | false => false
       | true => (andb2 b2 b3)
       end.
 
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check andb3.


Module NatPlayground.

Inductive nat: Type :=
   | O : nat
   | S : nat -> nat.
End NatPlayground.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Check (S(S(O))).


(* Exercise: 1 star (factorial)*)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n:nat):nat :=
   match n with
     | O => S(O)
     | S n' => mult (S n') (factorial n')
   end.

Compute (factorial (S(S(S(S(O)))))).
     

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.


Fixpoint leq0 (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' =>leq0 n' m'
            end
  end.




Fixpoint leq1 (n m :nat): bool :=
      match n with
        | O => true
        | S n'=> match m with
                   | O => false
                   | S m' => leq1 n' m'
                 end
     end.

Compute (leq1 (S(S(S(S(O))))) (S(S(S(S(O)))))).

(* Exercise: 1 star (blt nat)) *)


Definition blt_nat (n m : nat) : bool :=
     andb2 (leq1 n m) (negb (leq0 n m)).
                  

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4 ) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.


Theorem plus_0_: forall n :nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id: forall m n:nat,
 n=m ->
 n+n = m+m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.
