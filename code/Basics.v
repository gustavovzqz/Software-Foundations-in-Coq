(* First steps*)
Inductive day : Type := 
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day := 
  match d with 
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed. 



(* Booleans *)

Inductive bool : Type := 
  | true
  | false.

Definition negb (b: bool) : bool := 
  match b with 
  | true => false 
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) : bool := 
  match b1 with
  | true => b2
  | false => false 
  end. 

Definition orb (b1 b2 : bool) : bool := 
  match b1 with
  | true => true 
  | false => b2 
  end. 

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with 
  | true =>  match b2 with
             | true => false 
             | false => true 
             end
  | false => true
  end. 

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check true
  : bool.

Check negb.

Inductive rgb : Type :=
	| red
	| green
	| blue.

Inductive color : Type :=
	| black
	| white
	| primary (p : rgb).

Check primary.

Definition isred (c : color) : bool := 
	match c with
	| black => false 
	| white => false
	| primary red => true
	| primary _ => false
  end.

Compute isred (primary red).

Module Playground.
	Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.

Check b : bool.

Module NatPlayground.

Inductive nat : Type :=
  | O 
  | S (n : nat).

Check S(S(S(S(S(S(O)))))).

Definition pred (n : nat) : nat :=
	match n with
	| O => O
	| S n' => n'
	end.

End NatPlayground.

Compute S O. 

Definition minustwo (n : nat) : nat :=
  match n with 
  | S(S(n')) => n'
  | S(O) => O
  | O => O
  end.

Check minustwo.

Compute minustwo(4).

Check S. 


Fixpoint even (n : nat) : bool := 
  match n with 
  | O => true
  | S O => false 
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).
  
Compute even 4.

Example test_even_10: even 10 = true.
Proof. simpl. reflexivity. Qed. 

Example test_odd_10: odd 9 = true.
Proof. simpl. reflexivity. Qed. 


Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
	match n with 
	| O => m
	| S n' => S (plus n' m)
	end.

Fixpoint mult (n m : nat) : nat :=
	match n with 
	| O => O 
	| S n' => plus m (mult n' m)
	end.


Compute plus 10 3.

Compute mult 10 3.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m'=> minus n' m'
  end.

End NatPlayground2.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.



 Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
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

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  andb (leb n m) (negb (eqb n m)).


Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n'' : forall n : nat, 0 + n = n.
Proof. 
  intros m. reflexivity. Qed.

  Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.