Require Import BA.Basics.
Module NatList.

Inductive natprod: Type:=
  |pair: nat -> nat -> natprod.


Definition fst (s:natprod): nat:=
    match s with 
     | pair n _ => n
    end.

Check (pair 5 6).
Compute (fst (pair 4 3)).

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Check (pair 5 6).
Compute (fst (pair 4 3)).


Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* Exercise: 1 star (snd_fst_is_swap)*)

 Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.


(*Exercise: 1 star, optional (fst_swap_is_snd)*)

Theorem fst_swap_is_snd : forall(p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.


(* inductive definition of a list *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* a more  suitble Notation*)


Notation "x : l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 : (2 : (3 : nil)).
Definition mylist2 := 1 : 2 : 3 : nil.
Definition mylist3 := [1,2,3].


Fixpoint repeat (n count: nat): natlist:=
      match count with
        | O => []
        | S n' => n: repeat n n'
      end.   


Fixpoint length (xs : natlist): nat :=
      match xs with
       | [] => 0
       | (x:ys) => 1 + length ys
     end.

Compute (length [1,2,3,4,5]).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h : t => h : (app t l2)
  end.

Notation " xs ++ ys " := (app xs ys).
Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
      | [] => []
      | (x:xs) => match x with
                    |O => nonzeros xs
                    |S n => S n : nonzeros xs
                  end
   end.
  

Example test_nonzeros:
  nonzeros [0,1,0,2,3,0,0] = [1,2,3].
  reflexivity. Qed.


Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
      | [] => []
      |x:xs => match (evenb x) with
               |true => oddmembers xs
               |false => x:oddmembers xs
               end
    end.

Example test_oddmembers:
  oddmembers [0,1,0,2,3,0,0] = [1,3].
  reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
   length(oddmembers l).
  

Example test_countoddmembers1:
  countoddmembers [1,0,3,1,4,5] = 4.
   reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0,2,4] = 0.
   reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
   reflexivity. Qed.

 (* 
Exercise: 3 stars, advanced (alternate)*)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
     match l1  with
       |  [] => l2
       | (x:xs) => match l2 with
                    | [] =>( x:xs)
                    | (y:ys) => x: (y: alternate xs ys)
                    end
    end.
 

Example test_alternate1:
  alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
 reflexivity. Qed.

Compute (alternate [1,3,5,7] [2,4,6]).

Example test_alternate2:
  alternate [1] [4,5,6] = [1,4,5,6].
  reflexivity. Qed.

Example test_alternate3:
  alternate [1,2,3] [4] = [1,4,2,3].
  reflexivity. Qed.

Example test_alternate4:
  alternate [] [20,30] = [20,30].
  reflexivity. Qed.

Definition bag:= natlist.



Fixpoint count (v:nat) (s:bag) : nat:=
    match s with
     | [] => 0
     |(x:xs) => match (beq_nat x v) with
                | true => 1+ count v xs
                | false => count v xs
               end
    end.

Compute (count 1 [1,2,3,1,4,1]).
Example test_count1: count 1 [1,2,3,1,4,1] = 3.
 reflexivity. Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
 reflexivity. Qed.


Definition sum : bag -> bag -> bag :=
    app.


Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
   app (v:[]) s.
  

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
 simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1,4,1]) = 0.
simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
     match (count v (sum []  s)) with
       |O => false
       | _ => true
     end.
 

Example test_member1: member 1 [1,4,1] = true.
simpl. reflexivity. Qed. 

Example test_member2: member 2 [1,4,1] = false.
simpl. reflexivity. Qed.

(*proof some properteies over list *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    reflexivity.
    simpl. rewrite -> IHl1'. reflexivity. Qed.


Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h : t => rev t ++ [h]
  end.

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

(*---OPTIONS--*)


Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.


Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a : l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4,5,6,7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4,5,6,7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4,5,6,7] 9 = None.
Proof. reflexivity. Qed.



Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a : l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.


(*Exercise: 2 stars (hd_error) *)



Definition hd_error (l : natlist) : natoption:=
   match l with 
    | [] => None
    | (x:xs) => Some  x
   end.


Example test_hd_error1 : hd_error [] = None.
 Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
 Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5,6] = Some 5.
 Proof. reflexivity. Qed.

 (* Haskell -> Coq

  indexOf :: Int -> [Int] -> Maybe Int
indexOf _ []                 = Nothing
indexOf x (y:ys) | x == y    = Just 0
                 | otherwise = case indexOf x ys of
                                 Nothing -> Nothing
                                 Just i  -> Just (i + 1)   *)

Fixpoint indexOf (n:nat) (xs:natlist): natoption :=
     match xs with
      | [] => None
      | (y:ys) => match (beq_nat y n) with
                    | true => Some 0
                    |false => match (indexOf n ys) with
                                | None => None
                                | Some n => Some (S n)
                              end
                  end
    end.

Example indexOf1: (indexOf 3 [1,2,3]) = Some 2.
Proof. reflexivity. Qed.

End NatList.

















