(*
   This Coq file provides a formal verification of a 'find_max' function.
   The C function is defined as:
   int find_max(int nums[], int size) {
       int max = nums[0];
       for (int i = 1; i < size; i++) {
           if (nums[i] > max) {
               max = nums[i];
           }
       }
       return max;
   }
   
   Our Coq proof represents the C array as a list of integers (Z) and proves
   that the function's output is indeed the maximum element of the list.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

(*
   Formal definition of the find_max function in Coq.
   We represent the C array `int nums[]` as a `list Z` (list of integers).
   The `find_max_loop` function mirrors the C `for` loop, iterating
   through the list and maintaining the current maximum value.
*)
Definition find_max (nums : list Z) : Z :=
  match nums with
  | nil => 0
  | h :: t =>
    fix find_max_loop (l : list Z) (current_max : Z) : Z :=
      match l with
      | nil => current_max
      | x :: l' =>
        if Z.gt x current_max then
          find_max_loop l' x
        else
          find_max_loop l' current_max
    end t h
  end.

(*
   Formal definition of the property we want to prove.
   `IsMax` states that a value `m` is the maximum of a list `l` if:
   1. `m` is an element of the list (`In m l`).
   2. For every element `x` in the list, `m` is greater than or equal to `x` (`Z.le x m`).
*)
Inductive IsMax (l : list Z) (m : Z) : Prop :=
| is_max_intro :
    In m l ->
    (forall x, In x l -> Z.le x m) ->
    IsMax l m.

(*
   This is the main lemma that proves the correctness of our helper loop.
   It states that for any sublist `l` and any `current_max`, the result
   of the loop `find_max_loop l current_max` is the maximum of the
   original `current_max` and all elements in `l`.
*)
Lemma find_max_loop_is_max :
  forall (l : list Z) (current_max : Z),
  let result := find_max_loop l current_max in
  IsMax (current_max :: l) result.
Proof.
  intros l current_max.
  induction l as [| h t IHl].
  (* Base case: the list is empty (`nil`). *)
  - simpl.
    (* The result is `current_max`, the goal is `IsMax (current_max :: nil) current_max`. *)
    apply is_max_intro.
    + (* Proof that `current_max` is in the list `current_max :: nil`. *)
      left. reflexivity.
    + (* Proof that `current_max` is greater than or equal to all elements in the list. *)
      intros x Hx. destruct Hx.
      * reflexivity. (* If x is current_max, Z.le current_max current_max holds. *)
      * exfalso. exact H. (* The list has no other elements. *)
  
  (* Inductive step: the list is `h :: t`. *)
  - simpl.
    (* We proceed by case analysis on whether `h` is greater than `current_max`. *)
    destruct (Z.gt h current_max) eqn:Hgt.
    + (* Case 1: `h > current_max`. The new maximum is `h`. *)
      (* We apply the inductive hypothesis with the new maximum `h`. *)
      assert (IsMax (h :: t) (find_max_loop t h)).
      { eapply IHl. }
      clear IHl.
      apply is_max_intro.
      * (* Proof that the result is in the new list. *)
        destruct H as [Hin_h_t | H_le].
        { left. exact Hin_h_t. }
        { right. exact H. }
      * (* Proof that the result is greater than or equal to all elements. *)
        intros x Hx.
        destruct Hx as [Hx_eq | Hx_In].
        { (* Subcase: x is `current_max`. We need to show `Z.le current_max (find_max_loop t h)`. *)
          (* From the induction hypothesis, we know `Z.le h (find_max_loop t h)`. *)
          (* From `Hgt`, we know `Z.lt current_max h`. Transitivity proves the goal. *)
          eapply Z.le_trans. 1: lia. 2: apply H_le.
          exact Hx_eq.
        }
        { (* Subcase: x is in `h :: t`. This is directly given by the induction hypothesis. *)
          apply H_le. exact Hx_In.
        }
    + (* Case 2: `h <= current_max`. The maximum remains `current_max`. *)
      (* We use the original induction hypothesis. *)
      apply is_max_intro.
      * (* Proof that the result is in the new list. *)
        destruct IHl as [Hin_l | H_le].
        { right. exact Hin_l. }
        { right. exact Hin_l. }
      * (* Proof that the result is greater than or equal to all elements. *)
        intros x Hx.
        destruct Hx as [Hx_eq | Hx_In_t].
        { (* Subcase: x is `h`. We need `Z.le h (find_max_loop t current_max)`. *)
          (* We know `Z.le h current_max` because `Z.gt h current_max` is false. *)
          (* From the induction hypothesis, we know `Z.le current_max (find_max_loop t current_max)`. *)
          (* Transitivity proves the goal. *)
          eapply Z.le_trans. 1: lia. 2: destruct IHl as [Hin | H_le]. 2: exact H_le.
          exact Hx_eq.
        }
        { (* Subcase: x is in `current_max :: t`. This is given by the induction hypothesis. *)
          destruct IHl as [Hin | H_le]. exact H_le. exact Hx_In_t.
        }
Qed.

(*
   Main theorem: Prove that our `find_max` function correctly computes the maximum
   for any non-empty list.
   We assume the list is non-empty because the C function's behavior for an
   empty array is undefined (it would access `nums[0]`).
*)
Theorem find_max_correct :
  forall (nums : list Z),
  nums <> nil -> IsMax nums (find_max nums).
Proof.
  intros nums Hnonempty.
  (* The assumption `nums <> nil` allows us to deconstruct `nums` into `h :: t`. *)
  destruct nums as [| h t].
  - (* The empty list case is impossible due to `Hnonempty`. *)
    exfalso. apply Hnonempty. reflexivity.
  - (* The non-empty list case. *)
    simpl.
    (* The definition simplifies to `find_max_loop t h`.
       We can now apply the `find_max_loop_is_max` lemma directly. *)
    eapply find_max_loop_is_max.
Qed.
