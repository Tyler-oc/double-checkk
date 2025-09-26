Require Import Coq.Lists.List.
Require Import VST.floyd.proofauto.
Require Import vst_test.
Open Scope Z_scope.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* What it means to be the maximum of a list *)
Definition is_max (l: list Z) (m: Z) : Prop := In m l /\ forall x, In x l -> x <= m.

(* The (ident * funspec) pair for find_max *)
Definition find_max_spec : ident * funspec :=
  DECLARE _find_max
  WITH a: val, sh: share, contents: list Z, size: Z
  PRE [ tptr tint, tint ]
    PROP (readable_share sh;
          0 < Zlength contents;
          size = Zlength contents)
    PARAMS (a; Vint (Int.repr size))
    SEP (data_at sh (tarray tint (Z.to_nat size))
                 (map Vint (map Int.repr contents)) a)
  POST [ tint ]
    EX max: Z,
    PROP (is_max contents max)
    RETURN (Vint (Int.repr max))
    SEP (data_at sh (tarray tint (Z.to_nat size))
                 (map Vint (map Int.repr contents)) a).

(* Specification table *)
Definition Gprog : funspecs := [ find_max_spec ].

(* -------------------------------------------------- *)
(* Simple helper lemmas (completed proofs)            *)
(* -------------------------------------------------- *)

Lemma is_max_singleton: forall x, is_max [x] x.
Proof.
  intros x. unfold is_max. split.
  - simpl; auto.
  - intros y Hy. simpl in Hy. destruct Hy as [Hy|Hy].
    + subst; apply Z.le_refl.
    + contradiction.
Qed.

Lemma is_max_cons_gt:
  forall l x m,
    is_max l m ->
    (forall y, In y l -> y <= x) ->
    is_max (x :: l) x.
Proof.
  intros l x m [Hin Hle] Hbound. unfold is_max. split.
  - simpl. left; reflexivity.
  - intros y Hy. simpl in Hy. destruct Hy as [Hy|Hy].
    + subst; apply Z.le_refl.
    + apply Hbound. exact Hy.
Qed.

Lemma is_max_cons_le:
  forall l x m,
    is_max l m ->
    x <= m ->
    is_max (x :: l) m.
Proof.
  intros l x m Hmax Hle. unfold is_max in *. destruct Hmax as [Hin Hbound].
  split.
  - simpl. auto.
  - intros y Hy. simpl in Hy. destruct Hy.
    + subst. auto.
    + apply Hbound. auto.
Qed.

(* -------------------------------------------------- *)
(* LOOP INVARIANT for find_max                         *)
(* -------------------------------------------------- *)

Definition find_max_loop_inv (a: val) (sh: share)
                             (contents: list Z) (size: Z) :=
  EX i: Z, EX max_so_far: Z,
  PROP (1 <= i <= size;
        is_max (sublist 0 i contents) max_so_far)
  LOCAL (temp _max (Vint (Int.repr max_so_far));
         temp _nums a;
         temp _size (Vint (Int.repr size)))
  SEP (data_at sh (tarray tint (Z.to_nat size))
               (map Vint (map Int.repr contents)) a).

(* -------------------------------------------------- *)
(* THE MAIN PROOF                                      *)
(* -------------------------------------------------- *)

Lemma body_find_max: semax_body Vprog Gprog f_find_max find_max_spec.
Proof.
  start_function.
  (* max = nums[0]; *)
  forward.

  (* Important: forward_for_simple_bound expects a nat bound *)
  forward_for_simple_bound (Z.to_nat size) (find_max_loop_inv a sh contents size).
  - (* Loop precondition: invariant holds at i = 1 *)
    (* Use VST tactic `Exists` (capital E) to instantiate EX variables *)
    Exists 1. Exists (Znth 0 contents).
    entailer!.
    (* prove the is_max for sublist [0,1) *)
    apply is_max_singleton.

  - (* Loop body: preserve invariant *)
    Intros i max_so_far.
    (* we have 1 <= i <= size and is_max (sublist 0 i contents) max_so_far *)
    forward. (* load current_val = nums[i]; *)
    forward_if.
    + (* then branch: current_val > max_so_far *)
      forward. (* max = current_val; *)
      (* New invariant: i+1 and Znth i contents *)
      Exists (i + 1). Exists (Znth i contents).
      entailer!.
      (* We must show is_max (sublist 0 (i+1) contents) (Znth i contents) *)
      (* Use sublist_split: sublist 0 (i+1) = sublist 0 i ++ sublist i (i+1) *)
      rewrite sublist_split with (mid := i); try lia.
      simpl.
      (* Apply is_max_cons_gt: all elements in sublist 0 i are <= x := Znth i contents.
         We need to show ∀ y ∈ sublist 0 i, y <= Znth i contents. Use previous invariant and the branch hypothesis. *)
      apply is_max_cons_gt.
      * (* first arg: previous invariant gives is_max on sublist 0 i *)
        (* From PROP we have is_max (sublist 0 i contents) max_so_far *)
        simpl in H1. (* may expose the invariant; if not, use the name from entailer context *)
        (* H1 is the hypothesis name from entailer; introspect in interactive mode if different *)
        admit.
      * (* show every y in sublist 0 i <= Znth i contents *)
        intros y Hy.
        (* previous invariant: y <= max_so_far; branch condition: Znth i contents > max_so_far *)
        (* combine them to get y <= Znth i contents *)
        admit.

    + (* else branch: current_val <= max_so_far *)
      forward. (* skip *)
      Exists (i + 1). Exists max_so_far.
      entailer!.
      rewrite sublist_split with (mid := i); try lia.
      apply is_max_cons_le; auto; try lia.

  - (* After loop *)
    forward. (* return max; *)
    Intros i max_so_far.
    (* at exit i = size; use invariant to show is_max on full list *)
    entailer!.
    (* invariant gives is_max (sublist 0 i contents) max_so_far and i = size *)
    (* sublist 0 size = contents *)
    replace (sublist 0 i contents) with contents in H1.
    + exact H1.
    + (* show sublist 0 size = contents *)
      unfold sublist. (* or use sublist_same lemma *)
      apply sublist_same; lia.
Admitted.
