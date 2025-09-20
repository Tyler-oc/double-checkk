Require Import List.
Import ListNotations.
Require Import ZArith.

(* Find the maximum in a non-empty list of integers *)
Fixpoint find_max (l : list Z) : option Z :=
  match l with
  | [] => None
  | x :: xs =>
      match find_max xs with
      | None => Some x
      | Some m => Some (Z.max x m)
      end
  end.

(* Specification: m is the maximum of l *)
Definition is_max (l : list Z) (m : Z) :=
  In m l /\ forall x, In x l -> Z.le x m.

(* Example usage and proof outline *)
Example test_find_max :
  find_max [1%Z; 2%Z; 3%Z; 4%Z] = Some 4%Z.
Proof. reflexivity. Qed.