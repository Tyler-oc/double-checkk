Require Import VST.floyd.proofauto.
Require Import vst_test.
Open Scope Z_scope.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* Specification for is_greater: returns 1 if a > b, else 0 *)
Definition is_greater_spec : ident * funspec :=
  DECLARE _is_greater
  WITH a: Z, b: Z
  PRE [ tint, tint ]  (* Using older style parameter specification without OF *)
    PROP ()
    PARAMS (Vint (Int.repr a); Vint (Int.repr b))
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Vint (if zlt b a then Int.one else Int.zero))
    SEP ().

Definition Gprog : funspecs := [ is_greater_spec ].

Lemma body_is_greater: semax_body Vprog Gprog f_is_greater is_greater_spec.
Proof.
  start_function.
  forward.  (* return a > b; *)
  entailer!.  (* This solves the remaining verification conditions *)
Qed.