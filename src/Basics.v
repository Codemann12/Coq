

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
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

Definition andb (b1:bool) (b2:bool):bool :=
     match b1 with
       | true  => b2
       | false => false
       
       end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true  => true
  | false => b2
  end.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool:=
     match b1 with
       | false => false
       | true => (andb b2 b3)
       end.
 

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n')=> evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).  


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

Fixpoint plus (n m:nat):nat:=
   match n with
    | O => m 
    | S n' => S(plus n' m)
   end.


Compute (plus 5 4).

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


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' =>beq_nat n' m'
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
     andb (leq1 n m) (negb (beq_nat n m)).
                  

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4 ) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.


Theorem plus_0_n: forall n :nat, 0 + n = n.
Proof. 
  intros n.
  simpl.
  reflexivity.
  Qed.
     

Theorem plus_id: forall m n:nat,
 n=m ->
 n+n = m+m.
Proof.
 intros n m. 
 intros H.
 rewrite -> H. 
 reflexivity.
 Qed.

(*Exercise: 1 star (plus id exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o .
  intros H.
  intros G.
  rewrite -> H.
  rewrite -> G.
  reflexivity.
  Qed.


Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.


Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity. Qed.

(* exercise: 2 stars (mult S 1) *)


Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
   intros  n m .
   intros H. 
   rewrite -> H.
   reflexivity. Qed.



(*Exercise: 1 star (zero_nbeq_plus_1)*)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [|n'].
     reflexivity.
     reflexivity. Qed.

(* 
Exercise: 2 stars (andb_eq_orb)*)



Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) ->  b = c.
Proof.
  intros b c. destruct b.
   simpl. 
   intros H.
   rewrite -> H.
   reflexivity.
   simpl.
   intros G.
   rewrite -> G. reflexivity. Qed.


   
   


(* Exercise: 2 stars (andb_true_elim2) *)

Theorem andb_true_elim2 : forall b c :bool,
  andb b c = true -> 
  c = true.
Proof. intros b c . destruct b. simpl.
       intros H.
       rewrite -> H.
       reflexivity.   
       simpl.
       intros G.
       rewrite <- G.
       destruct c.
       rewrite -> G.
       reflexivity.
       reflexivity. Qed.
        (* a little bit long, but that's my best solution for now *)


Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.



(* Exercise: 2 starsM (boolean_functions)*)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
   intros f H b. rewrite -> H. rewrite -> H. reflexivity. Qed.


   



