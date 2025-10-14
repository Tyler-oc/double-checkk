Require Import List.
Require Import Arith.
Import ListNotations.

(* Helper function to find maximum of two natural numbers *)
Definition max_nat (a b : nat) : nat :=
  if a <=? b then b else a.

(* Alternative version that assumes non-empty list *)
Fixpoint find_max_nonempty (arr : list nat) : nat :=
  match arr with
  | [] => 0  (* Default case, though this violates precondition *)
  | [x] => x
  | x :: xs => max_nat x (find_max_nonempty xs)
  end.

(* Helper lemma about max_nat *)
Lemma max_nat_spec : forall a b,
  (max_nat a b = a /\ b <= a) \/ (max_nat a b = b /\ a <= b).
Proof.
  intros a b.
  unfold max_nat.
  destruct (a <=? b) eqn:Hab.
  - right. split.
    + reflexivity.
    + apply Nat.leb_le. assumption.
  - left. split.
    + reflexivity.
    + apply Nat.leb_nle in Hab.
      apply Nat.nle_gt in Hab.
      apply Nat.lt_le_incl.
      assumption.
Qed.

(* Helper lemma: max_nat a b is either a or b *)
Lemma max_nat_cases : forall a b,
  max_nat a b = a \/ max_nat a b = b.
Proof.
  intros a b.
  destruct (max_nat_spec a b) as [[H _] | [H _]].
  - left. assumption.
  - right. assumption.
Qed.

(* Helper lemma: both arguments are <= max_nat *)
Lemma max_nat_le_both : forall a b,
  a <= max_nat a b /\ b <= max_nat a b.
Proof.
  intros a b.
  destruct (max_nat_spec a b) as [[H1 H2] | [H1 H2]].
  - rewrite H1. split.
    + apply Nat.le_refl.
    + assumption.
  - rewrite H1. split.
    + assumption.
    + apply Nat.le_refl.
Qed.

(* Main theorem *)
Theorem find_max_nonempty_spec : forall (l : list nat),
  l <> [] ->
  let m := find_max_nonempty l in
  In m l /\ (forall x, In x l -> x <= m).
Proof.
  intros l Hne.
  induction l as [| h t IH].
  - (* Base case: empty list *)
    contradiction Hne. reflexivity.
  - (* Inductive case: h :: t *)
    simpl find_max_nonempty.
    destruct t as [| h' t'] eqn:Ht.
    + (* Case: singleton list [h] *)
      simpl. split.
      * left. reflexivity.
      * intros x Hin.
        destruct Hin as [Heq | Hfalse].
        -- rewrite <- Heq. apply Nat.le_refl.
        -- contradiction.
    + (* Case: h :: h' :: t' *)
      assert (Ht_ne : h' :: t' <> []) by discriminate.
      specialize (IH Ht_ne).
      simpl in IH.
      destruct IH as [IH_in IH_max].
      split.
      * (* Prove: In (max_nat h (find_max_nonempty (h' :: t'))) (h :: h' :: t') *)
        destruct (max_nat_cases h (find_max_nonempty (h' :: t'))) as [Hmax_h | Hmax_t].
        -- rewrite Hmax_h. left. reflexivity.
        -- rewrite Hmax_t. right. assumption.
      * (* Prove: forall x, In x (h :: h' :: t') -> x <= max_nat h (find_max_nonempty (h' :: t')) *)
        intros x Hin.
        destruct Hin as [Heq | Hin_tail].
        -- (* x = h *)
           rewrite <- Heq.
           destruct (max_nat_le_both h (find_max_nonempty (h' :: t'))) as [Hle _].
           assumption.
        -- (* In x (h' :: t') *)
           specialize (IH_max x Hin_tail).
           destruct (max_nat_le_both h (find_max_nonempty (h' :: t'))) as [_ Hle].
           apply (Nat.le_trans x (find_max_nonempty (h' :: t')) (max_nat h (find_max_nonempty (h' :: t')))).
           ++ assumption.
           ++ assumption.
Qed.