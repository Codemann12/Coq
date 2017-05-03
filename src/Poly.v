Require Import BA.NatList.
Require Import BA.Basics.

(* X is call a type argument*)
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check (list nat). (* (list nat : Set) *)

Fixpoint repeatP (X:Type) (n:nat) (x:X) : list X :=  
     match n with
      | O => nil X
      | S n => cons  X x (repeatP  X n x )
     end. 
                      

Example test_repeat :
  repeatP bool 1 false  = cons bool false (nil bool).
Proof. reflexivity. Qed.


 (* Exercise: 2 starsM (mumble_grumble) *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

 (* --> d (b a 5) is not well-typed because the actual type of X is not given.
The correct term should be (d mumble (b a 5))
    -->  (d mumble (b a 5))  this one is the solution above . 
    -->  (d bool (b a 5)) same scenario but with a different type (here bool). 
    -->  (e bool true) simple enough.
    -->  (e mumble (b c 0)) ok.
    -->  (e bool (b c 0)) can not match bool and numble
    -->  (c) same scenario as using a bool or any inductie type. false, 
true, O, S n*)


(* now let us make things more elegant with implicit argument. *)

Arguments nil {X}.
Arguments cons {X} _ _.



Fixpoint repeat0 {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count'=> cons x (repeat0 x count')
  end.

(* Haskell -> Coq

tails :: [a] -> [[a]]
tails []     = [[]]
tails (x:xs) = (x:xs) : tails xs *)

Fixpoint tails {X:Type} (xs:list X): list(list X):=
      match xs with
        | nil => nil 
        | (cons x xs) => cons (cons x xs) (tails xs)
      end.

Compute (tails (cons 1(cons 2(cons 3 nil)))).

Check @nil.



Fixpoint app {X:Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app xs l2)
  end.

Notation "x : y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Inductive prod (X Y: Type): Type :=
  |pair : X -> Y -> prod X Y.
 
Arguments pair {X}{Y}_ _.

Notation "( x , y )" := (pair x  y).


Notation "X * Y" := (prod X Y) : type_scope.



Definition fst {X Y : Type} (p: X*Y)  : X :=
  match p with
  | (x, y) => x
  end.



Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x : xs, y : ys => (x, y) : (combine xs ys)
  end.


(* Exercise: 2 stars, recommended (split).
This version of mine is not good enough because i used the list xys two times.
After having more experience i'll change it. *)


Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
   match l with
     | [] => ([], [])
     | ((x,y):xys) => ((x:(fst (split xys))), (y:snd (split xys)))
   end.

Compute (split [(1,false),(2,false)]).

Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity. Qed.



Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(* Exercise: 1 star, optional (hd_error_poly)*)

Definition hd_error {X : Type} (l : list X) : option X :=
    match l with
     | [] => None
     |(x:_) => Some x
    end.
 


Check @hd_error.

Example test_hd_error1 : hd_error [1,2] = Some 1.
 Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1],[2]] = Some [1].
 Proof. reflexivity. Qed.


(*Higher-Order Functions*)



Fixpoint filter {X:Type} (test: X-> bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h : t => if test h then h : (filter test t)
                        else filter test t
  end.

(* Exercise: 2 stars (filter_even_gt7) *)


(* the anonymous function fun should be used as the lambda function in Haskell *)

Definition filter_even_gt7 (l : list nat) : list nat:=
  filter (fun x => evenb x) (filter (fun n => leb 7 n ) l).



Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
  Proof. simpl. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
  Proof. reflexivity. Qed.


(* Exercise: 3 stars (partition) *)
Definition oddb (n:nat) : bool := negb (evenb n).

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
   ((filter test l), (filter (fun x  => negb (test x )) l)).
  

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
  Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
  Proof. reflexivity. Qed.



Fixpoint map {X Y:Type} (f: X -> Y) (xs:list X):list Y :=
    match xs with
     |[] => []
     | (x:ys) => f x: map f ys
    end.


(* Exercise: 2 stars, recommended (flat_map)*)


Fixpoint concat {X:Type} (xss:list(list X)): (list X):=
     match xss with
       |[] => []
       |(x:xs) => x  ++ (concat xs)
      end.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
    match l with
     | [] => []
     | xs => concat (map f xs)
    end.
     
Compute ( flat_map (fun n => [n,n,n]) [1,5,4]).

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
 Proof. reflexivity. Qed.



Fixpoint fold {X Y:Type} (f: X ->Y -> Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h : t => f h (fold f t b)
  end.

 (* Exercise: 3 starsM (fold_map)*)


Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
    fold (fun x res => f x: res) l [].

Compute(fold_map (fun x => x+1 )[1,2,3,4,5]).

Example fold_map0:
        fold_map (fun x => x+1 )[1,2,3,4,5]=[2,3,4,5,6].
Proof. reflexivity. Qed.


