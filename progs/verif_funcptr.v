Require Import VST.floyd.proofauto.
Require Import VST.progs.funcptr.

#[(*export, after Coq 8.13*)global] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope Z.
Local Open Scope logic.

Definition myspec :=
  WITH i: Z
  PRE [ tint ]
          PROP (Int.min_signed <= i < Int.max_signed)
          PARAMS (Vint (Int.repr i))
          SEP ()
  POST [ tint ]
         PROP() RETURN (Vint (Int.repr (i+1)))
          SEP().

Definition myfunc_spec := DECLARE _myfunc myspec.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [
    myfunc_spec; main_spec]).

Lemma body_myfunc: semax_body Vprog Gprog f_myfunc myfunc_spec.
Proof.
unfold myfunc_spec.
unfold myspec.
start_function.
forward.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function. fold cc_default noattr tint.
make_func_ptr _myfunc.
forward.

forward_call 3.
forward.
Qed.
