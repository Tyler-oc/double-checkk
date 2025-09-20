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

(* Example usage *)
Example test_find_max :
  find_max [1%Z; 2%Z; 3%Z; 4%Z] = Some 4%Z.
Proof. reflexivity. Qed.

(* Some helpful lemmas about Z.max *)
Lemma Z_max_spec : forall a b, Z.max a b = if Z_le_dec a b then b else a.
Proof.
  intros. destruct (Z_le_dec a b); reflexivity.
Qed.

Lemma Z_max_le_left : forall a b, Z.le a (Z.max a b).
Proof.
  intros. rewrite Z_max_spec.
  destruct (Z_le_dec a b); auto.
  apply Z.le_refl.
Qed.

Lemma Z_max_le_right : forall a b, Z.le b (Z.max a b).
Proof.
  intros.
  unfold Z.max.
  destruct (a ?= b)%Z eqn:Hcmp.
  - (* a = b *)
    apply Z.compare_eq in Hcmp. subst.
    apply Z.le_refl.
  - (* a < b *)
    apply Z.le_refl.
  - (* a > b *)
    apply Z.compare_gt_iff in Hcmp.
    apply Z.lt_le_incl.
    apply Z.gt_lt.
    assumption.
Qed.

(* Main correctness theorem for find_max *)
Theorem find_max_correct : forall l m,
  find_max l = Some m -> is_max l m.
Proof.
  intros l. induction l as [|x xs IH]; simpl.
  - (* Case: l = [] *)
    intros m H. discriminate H. (* Impossible case: empty list returns None *)
  
  - (* Case: l = x :: xs *)
    intros m H.
    destruct (find_max xs) eqn:E.
    
    + (* Subcase: find_max xs = Some z *)
      injection H as H'; subst m.
      unfold is_max; split.
      * (* Prove m is in the list *)
        rewrite Z_max_spec.
        destruct (Z_le_dec x z).
        -- (* x <= z, so max is z *)
           right. apply IH in E. destruct E as [InZ _]. assumption.
        -- (* z < x, so max is x *)
           left. reflexivity.
           
      * (* Prove m is >= all elements *)
        intros y InY.
        destruct InY as [EqY | InYs].
        -- (* y = x *)
           subst y. apply Z_max_le_left.
        -- (* y is in xs *)
           apply IH in E. destruct E as [_ MaxZ].
           specialize (MaxZ y InYs).
           apply Z.le_trans with z; auto.
           apply Z_max_le_right.
           
    + (* Subcase: find_max xs = None *)
      injection H as H'; subst m.
      unfold is_max; split.
      * (* Prove x is in the list *)
        left. reflexivity.
      * (* Prove x is >= all elements *)
        intros y [EqY | InYs].
        -- (* y = x *)
           subst y. apply Z.le_refl.
        -- (* y is in xs *)
           destruct xs.
           ++ (* xs = [] *)
              simpl in E. discriminate E.
           ++ (* xs = z :: zs *)
              simpl in E. discriminate E.
Qed.

(* Theorem showing that find_max returns None iff the list is empty *)
Theorem find_max_none : forall l,
  find_max l = None <-> l = [].
Proof.
  intro l. split.
  - (* -> direction *)
    destruct l as [|x xs].
    + (* l = [] *)
      intro H. reflexivity.
    + (* l = x :: xs *)
      simpl. destruct (find_max xs); intro H; discriminate H.
  - (* <- direction *)
    intro H. subst l. simpl. reflexivity.
Qed.

(* Combined theorem that fully characterizes find_max *)
Theorem find_max_characterization : forall l,
  (exists m, find_max l = Some m /\ is_max l m) \/ (l = [] /\ find_max l = None).
Proof.
  intro l.
  destruct (find_max l) eqn:E.
  - (* find_max l = Some z *)
    left. exists z. split; auto. apply find_max_correct; auto.
  - (* find_max l = None *)
    right. split.
    + apply find_max_none. auto.
    + auto.
Qed.