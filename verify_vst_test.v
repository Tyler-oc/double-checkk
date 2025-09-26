Require Import VST.floyd.proofauto.
Require Import vst_test.
Open Scope Z_scope.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* What it means to be the maximum of a list *)
Definition is_max (l: list Z) (m: Z) : Prop :=
  In m l /\ forall x, In x l -> x <= m.

(* The (ident * funspec) pair for find_max *)
Definition find_max_spec : ident * funspec :=
  DECLARE _find_max
  WITH a: val, sh: share, contents: list Z, size: Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh;
          0 < Zlength contents;
          size = Zlength contents)
    PARAMS (a; Vint (Int.repr size))
    SEP (data_at sh (tarray tint size)
                 (map Vint (map Int.repr contents)) a)
  POST [ tint ]
    EX max: Z,
    PROP (is_max contents max)
    RETURN (Vint (Int.repr max))
    SEP (data_at sh (tarray tint size)
                 (map Vint (map Int.repr contents)) a).

(* Specification table *)
Definition Gprog : funspecs := [ find_max_spec ].

(* -------------------------------------------------- *)
(* Simple helper lemmas (completed proofs)            *)
(* -------------------------------------------------- *)

Lemma is_max_singleton: forall x, is_max [x] x.
Proof.
  intros x. unfold is_max. split.
  - simpl. left; reflexivity.
  - intros y Hy. simpl in Hy. destruct Hy as [Hy|Hy].
    + subst; apply Z.le_refl.
    + contradiction.
Qed.

Lemma is_max_cons_gt: forall l x m,
  is_max l m -> (forall y, In y l -> y <= x) -> is_max (x :: l) x.
Proof.
  intros l x m [Hin Hle] Hbound. unfold is_max. split.
  - simpl. left; reflexivity.
  - intros y Hy. simpl in Hy. destruct Hy as [Hy|Hy].
    + subst; apply Z.le_refl.
    + apply Hbound; assumption.
Qed.

Lemma is_max_cons_le: forall l x m,
  is_max l m -> x <= m -> is_max (x :: l) m.
Proof.
  intros l x m Hmax Hle. unfold is_max in *. destruct Hmax as [Hin Hbound].
  split.
  - simpl. auto.
  - intros y Hy. simpl in Hy. destruct Hy.
    + subst. auto.
    + apply Hbound. auto.
Qed.

(* -------------------------------------------------- *)
(* LOOP INVARIANT for find_max *)
(* -------------------------------------------------- *)

Definition find_max_loop_inv (a: val) (sh: share)
                             (contents: list Z) (size: Z) :=
  EX i: Z, EX max_so_far: Z,
  PROP (1 <= i <= size;
        is_max (sublist 0 i contents) max_so_far)
  LOCAL (temp _max (Vint (Int.repr max_so_far));
         temp _nums a;
         temp _size (Vint (Int.repr size)))
  SEP (data_at sh (tarray tint size)
               (map Vint (map Int.repr contents)) a).

(* -------------------------------------------------- *)
(* THE MAIN PROOF *)
(* -------------------------------------------------- *)

Lemma body_find_max: semax_body Vprog Gprog f_find_max find_max_spec.
Proof.
  start_function.
  forward. (* max = nums[0]; *)

  forward_for_simple_bound size (find_max_loop_inv a sh contents size).
  - (* Loop precondition: prove invariant holds for i=1 *)
    exists 1, (Znth 0 contents).
    entailer!.
    apply is_max_singleton.

  - (* Loop body: prove invariant is preserved *)
    Intros i max_so_far.
    forward. (* current_val = nums[i]; *)
    forward_if.
    + (* Then branch: current_val > max_so_far *)
      forward. (* max = current_val; *)
      Exists (i+1), (Znth i contents).
      entailer!.
      rewrite sublist_split with (mid := i); try omega.
      apply is_max_cons_gt.
      * auto.
      * intros y Hy.
        specialize (H2 y Hy).
        apply Z.le_trans with max_so_far; auto.
        omega.

    + (* Else branch: current_val <= max_so_far *)
      forward. (* else: skip *)
      Exists (i+1), max_so_far.
      entailer!.
      rewrite sublist_split with (mid := i); try omega.
      apply is_max_cons_le; auto.
      omega.

  - (* After the loop *)
    Intros i max_so_far.
    forward. (* return max; *)
    Exists max_so_far.
    entailer!.
    rewrite sublist_same in H2; auto.
Qed.