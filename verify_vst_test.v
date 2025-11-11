Require Import Coq.Lists.List.
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

(* Helper: compute maximum of first i elements *)
Fixpoint Zmax_of_list (l: list Z) : Z :=
  match l with
  | [] => Int.min_signed
  | [x] => x
  | x :: xs => Z.max x (Zmax_of_list xs)
  end.

(* Helper lemmas about Zmax_of_list and sublist *)
Lemma Zmax_of_list_In : forall l,
  l <> [] -> In (Zmax_of_list l) l.
Proof.
  induction l; intros.
  - contradiction.
  - simpl. destruct l.
    + left; reflexivity.
    + destruct (Z.max_spec a (Zmax_of_list (z :: l))) as [[H1 H2]|[H1 H2]];
      rewrite H2.
      * right. apply IHl. discriminate.
      * left; reflexivity.
Qed.

Lemma Zmax_of_list_upper_bound : forall l x,
  In x l -> x <= Zmax_of_list l.
Proof.
  induction l; intros.
  - inversion H.
  - simpl in *. destruct l.
    + destruct H; subst; try contradiction.
      apply Z.le_refl.
    + destruct H; subst.
      * apply Z.le_max_l.
      * etransitivity.
        -- apply IHl. assumption.
        -- apply Z.le_max_r.
Qed.

Lemma Zmax_of_list_is_max : forall l,
  l <> [] -> is_max l (Zmax_of_list l).
Proof.
  intros. split.
  - apply Zmax_of_list_In. assumption.
  - intros. apply Zmax_of_list_upper_bound. assumption.
Qed.

Lemma is_max_sublist_extension : forall contents i max_i x,
  0 <= i < Zlength contents ->
  is_max (sublist 0 i contents) max_i ->
  x = Znth i contents 0 ->
  is_max (sublist 0 (i + 1) contents) (Z.max max_i x).
Proof.
  intros contents i max_i x Hi Hmax_i Hx.
  destruct Hmax_i as [Hin Hbound].
  split.
  - (* In (Z.max max_i x) (sublist 0 (i + 1) contents) *)
    destruct (Z.max_spec max_i x) as [[Hle Heq]|[Hle Heq]]; rewrite Heq.
    + apply In_sublist_In with (i0 := 0) (j := i); auto.
      * list_solve.
      * list_solve.
    + subst x. apply In_Znth with (i := i).
      * rewrite Zlength_sublist; list_solve.
      * rewrite Znth_sublist; list_solve.
  - (* forall y, In y (sublist 0 (i + 1) contents) -> y <= Z.max max_i x *)
    intros y Hy.
    rewrite sublist_split with (mid := i) in Hy by list_solve.
    apply in_app_or in Hy. destruct Hy as [Hy_left | Hy_right].
    + (* y in first part *)
      specialize (Hbound y Hy_left).
      etransitivity; [exact Hbound | apply Z.le_max_l].
    + (* y in second part [Znth i contents] *)
      rewrite sublist_one in Hy_right by list_solve.
      simpl in Hy_right. destruct Hy_right as [Heq | []]; subst.
      rewrite Hx. apply Z.le_max_r.
Qed.

Lemma is_max_complete_list : forall contents max_val,
  is_max (sublist 0 (Zlength contents) contents) max_val ->
  is_max contents max_val.
Proof.
  intros. rewrite sublist_same in H by list_solve. assumption.
Qed.

(* Key lemma: extending sublist by one element *)
Lemma Zmax_of_list_snoc : forall l x,
  l <> [] ->
  Zmax_of_list (l ++ [x]) = Z.max (Zmax_of_list l) x.
Proof.
  induction l; intros.
  - contradiction.
  - simpl. destruct l.
    + simpl. rewrite Z.max_comm. reflexivity.
    + simpl in IHl.
      rewrite IHl by discriminate.
      apply Z.max_assoc.
Qed.

Lemma Zmax_of_list_sublist_next : forall contents i,
  0 <= i < Zlength contents ->
  Zmax_of_list (sublist 0 (i + 1) contents) =
  Z.max (Zmax_of_list (sublist 0 i contents)) (Znth i contents 0).
Proof.
  intros.
  destruct (Z.eq_dec i 0).
  - subst. rewrite sublist_0_cons by list_solve.
    rewrite sublist_nil_gen by lia.
    simpl. rewrite Z.max_comm. reflexivity.
  - rewrite sublist_split with (mid := i) by list_solve.
    rewrite sublist_one by list_solve.
    rewrite Zmax_of_list_snoc.
    + reflexivity.
    + intro Hcontra.
      rewrite Zlength_sublist in Hcontra by list_solve.
      lia.
Qed.

(* Main proof *)
Lemma body_find_max: semax_body Vprog Gprog f_find_max find_max_spec.
Proof.
  start_function.
  
  (* max = nums[0] *)
  forward.
  
  (* Loop from i=1 to size *)
  forward_for_simple_bound size
    (EX i: Z,
      PROP ()
      LOCAL (temp _max (Vint (Int.repr (Zmax_of_list (sublist 0 i contents))));
             temp _size (Vint (Int.repr size));
             temp _nums a)
      SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a)).
  
  - (* Establish invariant: i = 1 initially *)
    entailer!.
    rewrite sublist_one by list_solve.
    simpl. reflexivity.
  
  - (* Loop body preserves invariant *)
    forward. (* Load nums[i] *)
    forward_if. (* if (nums[i] > max) *)
    
    + (* Then branch: nums[i] > max, so update max *)
      forward. (* max = nums[i] *)
      entailer!.
      f_equal. f_equal.
      rewrite Zmax_of_list_sublist_next by lia.
      rewrite Z.max_r by lia.
      reflexivity.
    
    + (* Else branch: nums[i] <= max, so keep max *)
      entailer!.
      f_equal. f_equal.
      rewrite Zmax_of_list_sublist_next by lia.
      rewrite Z.max_l by lia.
      reflexivity.
  
  - (* After loop: prove postcondition *)
    forward. (* return max *)
    Exists (Zmax_of_list (sublist 0 size contents)).
    entailer!.
    + (* Prove is_max contents (Zmax_of_list contents) *)
      assert (sublist 0 size contents = contents) as Heq.
      { rewrite sublist_same by list_solve. reflexivity. }
      rewrite Heq.
      apply Zmax_of_list_is_max.
      intro Hcontra. subst contents. simpl in H. lia.
Qed.