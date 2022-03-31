From compcert Require Export common.AST cfrontend.Ctypes cfrontend.Clight.
Export Cop.
Require Export VST.floyd.base2.
Require Export VST.floyd.functional_base.
Require Export VST.floyd.client_lemmas.
Require Export VST.floyd.go_lower.
Require Export VST.floyd.closed_lemmas.
Require Export VST.floyd.compare_lemmas.
Require Export VST.floyd.semax_tactics.
Require Export VST.floyd.entailer.
Require Export VST.floyd.forward. (* must come after entailer because of Ltac override *)
Require Export VST.floyd.subsume_funspec.
Require Export VST.floyd.call_lemmas.
Require Export VST.floyd.forward_lemmas.
Require Export VST.floyd.for_lemmas.
Require Export VST.floyd.nested_pred_lemmas.
Require Export VST.floyd.nested_field_lemmas.
Require Export VST.floyd.efield_lemmas.
Require Export VST.floyd.mapsto_memory_block.
Require Export VST.floyd.aggregate_type.
Require VST.floyd.aggregate_pred. Export floyd.aggregate_pred.aggregate_pred.
Require Export VST.floyd.reptype_lemmas.
Require Export VST.floyd.simpl_reptype.
Require Export VST.floyd.data_at_rec_lemmas.
Require Export VST.floyd.field_at.
Require Export VST.floyd.field_at_wand.
Require Export VST.floyd.field_compat.
Require Export VST.floyd.stronger.
Require Export VST.floyd.loadstore_mapsto.
Require Export VST.floyd.loadstore_field_at.
Require Export VST.floyd.nested_loadstore.
Require Export VST.floyd.local2ptree_denote.
Require Export VST.floyd.local2ptree_eval.
Require Export VST.floyd.local2ptree_typecheck.
Require Export VST.floyd.proj_reptype_lemmas.
Require Export VST.floyd.replace_refill_reptype_lemmas.
Require Export VST.floyd.sc_set_load_store.
Require Export VST.floyd.unfold_data_at.
Require Export VST.floyd.globals_lemmas.
Require Export VST.floyd.diagnosis.
Require Export VST.floyd.freezer.
Require Export VST.floyd.deadvars.
Require Export VST.floyd.hints.
Require Export VST.floyd.Clightnotations.
Require Export VST.floyd.data_at_list_solver.
Require Export VST.floyd.data_at_lemmas.
Require VST.msl.iter_sepcon.
Require VST.msl.wand_frame.
Require VST.msl.wandQ_frame.
Require VST.floyd.linking.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Set Ltac2 Backtrace.

(*funspec scope is the default, so remains open.
  User who wnt ot use old funspecs should 
  "Require Import Require Import VST.floyd.Funspec_old_Notation."
  Global Close Scope funspec_scope.*)

Arguments semax {CS} {Espec} Delta Pre%assert cmd%C Post%assert.
Export ListNotations.
Export Clight_Cop2.
 
(*after Coq 8.13: #[export]*) Hint Rewrite add_repr mul_repr sub_repr : entailer_rewrite.
(*after Coq 8.13: #[export]*) Hint Rewrite ptrofs_add_repr ptrofs_mul_repr ptrofs_sub_repr : entailer_rewrite.
(*after Coq 8.13: #[export]*) Hint Rewrite mul64_repr add64_repr sub64_repr or64_repr and64_repr : entailer_rewrite.
(*after Coq 8.13: #[export]*) Hint Rewrite neg_repr neg64_repr : entailer_rewrite.
(*after Coq 8.13: #[export]*) Hint Rewrite ptrofs_to_int_repr: entailer_rewrite norm.
(*after Coq 8.13: #[export]*) Hint Rewrite ptrofs_to_int64_repr using reflexivity: entailer_rewrite norm.

Lemma Vptrofs_unfold_false: 
Archi.ptr64 = false -> Vptrofs = fun x => Vint (Ptrofs.to_int x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma Vptrofs_unfold_true: 
Archi.ptr64 = true -> Vptrofs = fun x => Vlong (Ptrofs.to_int64 x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma modu_repr: forall x y, 
   0 <= x <= Int.max_unsigned ->
   0 <= y <= Int.max_unsigned ->
  Int.modu (Int.repr x) (Int.repr y) = Int.repr (x mod y).
Proof.
intros. unfold Int.modu. rewrite !Int.unsigned_repr by auto. auto.
Qed.
(*after Coq 8.13: #[export]*) Hint Rewrite modu_repr using rep_lia : entailer_rewrite norm.

(*after Coq 8.13: #[export]*) Hint Rewrite Vptrofs_unfold_false using reflexivity: entailer_rewrite norm.
(*after Coq 8.13: #[export]*) Hint Rewrite Vptrofs_unfold_true using reflexivity: entailer_rewrite norm.

#[export] Hint Extern 1 (Vundef = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = Vundef) => reflexivity : cancel.
#[export] Hint Extern 1 (repeat Vundef _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = repeat _ Vundef) => reflexivity : cancel.
#[export] Hint Extern 1 (Vundef :: _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = Vundef :: _) => reflexivity : cancel.
#[export] Hint Extern 1 (@nil _ = default_val _) => reflexivity : cancel.
#[export] Hint Extern 1 (default_val _ = @nil _) => reflexivity : cancel.

#[(*export, after Coq 8.13*)global] Instance Inhabitant_mpred : Inhabitant mpred := @FF mpred Nveric.
#[(*export, after Coq 8.13*)global] Instance Inhabitant_share : Inhabitant share := Share.bot.

Arguments deref_noload ty v / .
Arguments nested_field_array_type {cs} t gfs lo hi / .
Arguments nested_field_type {cs} t gfs / .  (* redundant? *)
Arguments nested_field_offset {cs} t gfs / .  (* redundant? *)
Arguments Z.mul !x !y.
Arguments Z.sub !m !n.
Arguments Z.add !x !y.
Global Transparent peq.
Global Transparent Archi.ptr64.

#[export] Hint Resolve readable_Ers : core.

Ltac EExists_unify1 x P :=
 match P with
 | ?P1 /\ ?P2 => first [EExists_unify1 x P1 | EExists_unify1 x P2]
 | ?A = ?B =>
  match A with context [x] =>
  pattern (A=B);
  let y := fresh "y" in match goal with |- ?F _ => set (y:=F) end;
  autorewrite with entailer_rewrite;
  first  [subst x; match goal with |- _ (?A' = ?B') => unify A' B' end
  | match goal with
  | x:= ?u |- _ (Vint (Int.repr (x - ?i)) = Vint (Int.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vint (Int.repr (x + ?i)) = Vint (Int.repr ?j)) =>
        unify u (j-i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x - ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x + ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j-i); subst x
  end];
  subst y; cbv beta
  end
end.

Ltac EExists_unify := 
  let T := fresh "T"  in
  let x := fresh "x" in
  evar (T:Type); evar (x:T); subst T; 
  Exists x;
  match goal with
  | |- _ |-- !! ?P && _ => EExists_unify1 x P
  | |- _ |-- !! ?P => EExists_unify1 x P
  end.

Ltac simpl_implicit :=
  simpl projT1.

Ltac step :=
  first
  [ progress Intros
  | let x := fresh "x" in Intros x
  | progress simpl_implicit
  | progress autorewrite with sublist in *|-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_lia | cstring' | Zlength_solve
  | match goal with |- ENTAIL _, _ |-- _ =>  go_lower end
  | EExists_unify
  | cstring1
  | deadvars!
  | solve [match goal with |- @derives mpred _ _ _ => cancel end]
  | solve [entailer!; try cstring']
  | list_solve
  ].

Tactic Notation "step!"  :=
  first
  [ progress Intros
  | let x := fresh "x" in
    Intros x
  | progress simpl_implicit
  | progress autorewrite with sublist in * |-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_lia
  | cstring'
  | Zlength_solve
  | EExists
  | cstring1
  | deadvars!
  | progress_entailer
  (* | match goal with |- _ /\ _ => split end *)
  | list_solve
  ].

Tactic Notation "info_step!" :=
  first
  [ progress Intros; idtac "Intros."
  | let x := fresh "x" in
    Intros x;
    idtac "Intros x."
  | progress simpl_implicit; idtac "simpl_implicit."
  | progress autorewrite with sublist in * |-; idtac "autorewrite with sublist in * |-."
  | progress autorewrite with sublist; idtac "autorewrite with sublist."
  | progress autorewrite with norm; idtac "autorewrite with norm."
  | forward; idtac "forward."
  | forward_if; idtac "forward_if."
  | forward_call; idtac "forward_call."
  | rep_lia; idtac "rep_lia."
  | cstring'; idtac "cstring'."
  | Zlength_solve; idtac "Zlength_solve."
  | EExists; idtac "EExists."
  | cstring1; idtac "cstring1."
  | deadvars!; idtac "deadvars!."
  | progress_entailer; idtac "progress_entailer."
  (* | match goal with |- _ /\ _ => split end; idtac "split." *)
  | list_solve; idtac "list_solve."
  ].

Ltac2 mutable zn_debug := true.

Ltac2 zn_log (msg : string) :=
  match zn_debug with
  | true => Message.print (Message.of_string msg)
  | false => ()
  end.

Ltac ex_intros :=
  lazymatch goal with
  | |- semax _ ?x _ _ =>
    lazymatch x with
    | context [EX exname, _] =>
      let name := fresh exname in Intros name
    end
  | |- EX exname, _ |-- _ =>
    let name := fresh exname in Intros name
  end.

Ltac2 newstep () :=
  try (progress ltac1:(Intros); zn_log "Intros.");
  try (ltac1:(ex_intros); zn_log "ex_intros.");
  first
  [ ltac1:(forward); zn_log "forward."
  | ltac1:(forward_if); zn_log "forward_if."
  | ltac1:(forward_call); zn_log "forward_call."
  ].

Ltac newstep := ltac2:(newstep ()).

Ltac zn_semax_pre_simpl := fail.
Ltac zn_semax_post_simpl := fail.

(* Performs a "single-step" for fastforward *)
Ltac2 fastforward_ss () :=
  first
  [ progress ltac1:(Intros); zn_log "Intros."
  | ltac1:(ex_intros); zn_log "ex_intros."
  | progress ltac1:(simpl_implicit); zn_log "simpl_implicit."
  | progress ltac1:(zn_semax_pre_simpl)
  | lazy_match! goal with [ |- _ |-- EX _, _ ] => 
    first
    [ ltac1:(EExists_unify); zn_log "EExists_unify."
    | ltac1:(EExists); zn_log "EExists."
    ]
    end
  | ltac1:(forward); zn_log "forward."
  | ltac1:(forward_if); zn_log "forward_if."
  | ltac1:(forward_call); zn_log "forward_call."
  | ltac1:(cstring1); zn_log "cstring1."
  | ltac1:(progress_entailer); zn_log "progress_entailer."
  | progress ltac1:(autorewrite with norm); zn_log "autorewrite with norm."
  (*| match goal with |- ENTAIL _, _ |-- _ =>  go_lower end; idtac "go_lower."*)
  | progress ltac1:(autorewrite with sublist in * |-); zn_log "autorewrite with sublist in * |-."
  | progress ltac1:(autorewrite with sublist); zn_log "autorewrite with sublist."
  | progress ltac1:(zn_semax_post_simpl)
  (* | lazy_match! goal with [ |- context [if _ then _ else _] ] => ltac1:(if_tac) end; print (of_string "if_tac.") *)
  ].

Ltac2 fastforward_ss' () :=
  first
  [ progress ltac1:(Intros); zn_log "Intros."
  | ltac1:(ex_intros); zn_log "ex_intros."
  | progress ltac1:(simpl_implicit); zn_log "simpl_implicit."
  | progress ltac1:(zn_semax_pre_simpl)
  | progress ltac1:(autorewrite with norm); zn_log "autorewrite with norm."
  | progress ltac1:(autorewrite with sublist); zn_log "autorewrite with sublist."
  | progress ltac1:(autorewrite with sublist in * |-); zn_log "autorewrite with sublist in * |-."
  | lazy_match! goal with [ |- _ |-- EX _, _ ] => 
    first
    [ ltac1:(EExists_unify); zn_log "EExists_unify."
    | ltac1:(EExists); zn_log "EExists."
    ]
    end
  | ltac1:(cstring1); zn_log "cstring1."
  | ltac1:(forward); zn_log "forward."
  | ltac1:(forward_if); zn_log "forward_if."
  | ltac1:(forward_call); zn_log "forward_call."
  | ltac1:(progress_entailer); zn_log "progress_entailer."
  (*| match goal with |- ENTAIL _, _ |-- _ =>  go_lower end; idtac "go_lower."*)
  | progress ltac1:(zn_semax_post_simpl)
  (* | lazy_match! goal with [ |- context [if _ then _ else _] ] => ltac1:(if_tac) end; print (of_string "if_tac.") *)
  ].

Ltac ss''' :=
  first
  [ progress Intros; idtac "Intros."
  | lazymatch goal with
    | |- semax _ (PROPx _ (LOCALx _ (SEPx ?X))) _ _=>
      lazymatch X with
      | context [EX X', _] =>
        let x := fresh X' in Intros x
      end
    end
  | progress simpl_implicit; idtac "simpl_implicit."
  | zn_semax_pre_simpl
  | progress autorewrite with sublist in * |-; idtac "autorewrite with sublist in * |-."
  | progress autorewrite with sublist; idtac "autorewrite with sublist."
  | progress autorewrite with norm; idtac "autorewrite with norm."
  | forward; idtac "forward."
  | forward_if; idtac "forward_if."
  | forward_call; idtac "forward_call."
  | EExists_unify; idtac "EExists_unify"
  | match goal with |- _ |-- EX _, _ => EExists end; idtac "EExists."
  | progress_entailer; idtac "progress_entailer."
  | match goal with |- ENTAIL _, _ |-- _ =>  go_lower end; idtac "go_lower."
  | match goal with |- context[if _ then _ else _] => if_tac end; idtac "if_tac."
  | zn_semax_post_simpl
  ].

Ltac2 Type agro_lvl := [ Safe | Med | Slow ].

Ltac2 simplstep (agro : agro_lvl) :=
  match agro with
  | Safe => fastforward_ss ()
  | Med => fastforward_ss' ()
  | Slow => ltac1:(ss''')
  end.

Ltac2 fastforward (agro : agro_lvl) :=
  progress (
    try (lazy_match! goal with
    | [ |- semax_body _ _ _ _ ] =>
      try (progress ltac1:(leaf_function); zn_log "leaf_function");
      ltac1:(start_function); zn_log "start_function."
    end);
    repeat (lazy_match! goal with
    | [ |- semax _ _ _ _ ] => simplstep agro
    | [ |- _ ] => ltac1:(clear_MORE_POST)
    end)
  ).

(* Ltac2 Notation "fastforward" dbs(opt(seq("with", hintdb))) :=
  fastforward' dbs. *)

Ltac fastforward := ltac2:(fastforward Safe).
Tactic Notation "fastforward!" := ltac2:(fastforward Med).
Tactic Notation "fastforward!!" := ltac2:(fastforward Slow).

Local Tactic Notation "smp" tactic(custom_simpl) "with" ident(hintdb) :=
  repeat first
  [(* progress simpl; idtac "simpl."
  |*) progress custom_simpl
  | progress autorewrite with hintdb; idtac "autorewrite with hintdb."
  | progress autorewrite with hintdb in * |-; idtac "autorewrite with hintdb in * |-."
  | progress autorewrite with sublist in * |-; idtac "autorewrite with sublist in * |-."
  | progress autorewrite with sublist; idtac "autorewrite with sublist."
  | progress autorewrite with norm; idtac "autorewrite with norm. (finish'')"
  ].

Ltac zn_pre_solve_simpl := fail.
Ltac zn_retry_solve_simpl := fail.
Ltac zn_fast_solve := fail.
Ltac zn_slow_solve := fail.
Ltac zn_entailer_solve := fail.

Ltac inst_exists :=
  repeat lazymatch goal with
  | |- exists i : _, _ => eexists + exists i
  end.


Ltac2 mutable zn_decisive_values () : constr list := [
  'true; 'false; 'nullval
].

Ltac2 subst_decisives () := Control.enter (fun () =>
  List.iter (fun c =>
    repeat (
      match! goal with
      | [ h : ?x = ?y |- _ ] =>
        match Constr.equal c x with
        | true => ltac1:(y |- subst y) (Ltac1.of_constr y)
        | false =>
          match Constr.equal c y with
          | true => ltac1:(x |- subst x) (Ltac1.of_constr x)
          | false => fail
          end
        end
      end
    )
  ) (zn_decisive_values ())).

Local Ltac2 rec get_root (c : constr) :=
  lazy_match! c with
  | ?f _ => get_root f
  | _ => c
  end.

Local Ltac2 f_equal_root () :=
  lazy_match! goal with
  | [ |- ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ ] => get_root f
  | [ |- ?f _ _ _ _ _ = ?f _ _ _ _ _ ] => get_root f
  | [ |- ?f _ _ _ _ = ?f _ _ _ _ ] => get_root f
  | [ |- ?f _ _ _ = ?f _ _ _ ] => get_root f
  | [ |- ?f _ _ = ?f _ _ ] => get_root f
  | [ |- ?f _ = ?f _ ] => get_root f
  end.

Local Theorem Val_of_bool_inj : forall x y, Val.of_bool x = Val.of_bool y -> x = y.
Proof.
intros [] [] H; try discriminate; reflexivity.
Qed.

Ltac2 mutable zn_injective_functions () : (constr * constr) list :=
  [ ('Val.of_bool, 'Val_of_bool_inj) ].

Ltac2 f_equal_check () := Control.enter (fun () =>
  let root := f_equal_root () in
  if Constr.is_constructor root
  then f_equal
  else 
    let injs := zn_injective_functions () in
    match List.find_opt (fun (c, _) => Constr.equal c root) injs with
    | Some _ => f_equal
    | None => fail
    end).

Ltac2 check_args' (c : constr) (i : int) : bool :=
  lazy_match! Constr.type c with
  | _ -> _ -> _ -> _ -> _ -> _ -> _ => Int.equal i 6
  | _ -> _ -> _ -> _ -> _ -> _ => Int.equal i 5
  | _ -> _ -> _ -> _ -> _ => Int.equal i 4
  | _ -> _ -> _ -> _ => Int.equal i 3
  | _ -> _ -> _ => Int.equal i 2
  | _ -> _ => Int.equal i 1
  end.

Ltac2 rec check_args_aux (t : constr) (i : int) : bool :=
  if Int.lt i 0
  then false
  else
    lazy_match! t with
    | _ -> ?t' => check_args_aux t' (Int.sub i 1)
    | _ => Int.equal i 0
    end
.

Ltac2 check_args (c : constr) (i : int) : bool :=
  check_args_aux (Constr.type c) i.

Ltac2 inj_check () :=
  if List.for_all (fun (c, p) =>
    lazy_match! Constr.type p with
    | forall x1 x2 x3 x4 x5 x6 y1 y2 y3 y4 y5 y6,
        ?f x1 x2 x3 x4 x5 x6 = ?f y1 y2 y3 y4 y5 y6 ->
        x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4 /\ x5 = y5 /\ x6 = y6
          => Bool.and (Constr.equal c (get_root f)) (check_args c 6)
    | forall x1 x2 x3 x4 x5 y1 y2 y3 y4 y5,
        ?f x1 x2 x3 x4 x5 = ?f y1 y2 y3 y4 y5 ->
        x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4 /\ x5 = y5
          => Bool.and (Constr.equal c (get_root f)) (check_args c 5)
    | forall x1 x2 x3 x4 y1 y2 y3 y4,
        ?f x1 x2 x3 x4 = ?f y1 y2 y3 y4 ->
        x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4
          => Bool.and (Constr.equal c (get_root f)) (check_args c 4)
    | forall x1 x2 x3 y1 y2 y3,
        ?f x1 x2 x3 = ?f y1 y2 y3 ->
        x1 = y1 /\ x2 = y2 /\ x3 = y3
          => Bool.and (Constr.equal c (get_root f)) (check_args c 3)
    | forall x1 x2 y1 y2,
        ?f x1 x2 = ?f y1 y2 ->
        x1 = y1 /\ x2 = y2
          => Bool.and (Constr.equal c (get_root f)) (check_args c 2)
    | forall x y,
        ?f x = ?f y ->
        x = y
          => Bool.and (Constr.equal c (get_root f)) (check_args c 1)
    end
  ) (zn_injective_functions ())
  then ()
  else fail.

Ltac2 simpl_plain_goal () :=
  repeat (first
  [ progress intros; zn_log "intros."
  | constructor; zn_log "constructor."
  | progress ltac1:(simpl_implicit); zn_log "simpl_implicit."
  | progress (subst_decisives ()); zn_log "subst_decisives."
  | progress ltac1:(zn_pre_solve_simpl)
  | progress ltac1:(inst_exists); zn_log "inst_exists."
  | lazy_match! goal with
    | [ |- _ < _ < _ ] => first
      [ ltac1:(rep_lia); zn_log "rep_lia."
      | split; zn_log "split."; try (ltac1:(rep_lia); zn_log "rep_lia.")
      ]
    | [ |- _ <= _ < _ ] => first
      [ ltac1:(rep_lia); zn_log "rep_lia."
      | split; zn_log "split."; try (ltac1:(rep_lia); zn_log "rep_lia.")
      ]
    | [ |- _ < _ <= _ ] => first
      [ ltac1:(rep_lia); zn_log "rep_lia."
      | split; zn_log "split."; try (ltac1:(rep_lia); zn_log "rep_lia.")
      ]
    | [ |- _ <= _ <= _ ] => first
      [ ltac1:(rep_lia); zn_log "rep_lia."
      | split; zn_log "split."; try (ltac1:(rep_lia); zn_log "rep_lia.")
      ]
    end
  | progress cbn; zn_log "cbn."
  ]).

Ltac2 finish_quick () :=
  first
  [ ltac1:(contradiction); zn_log "contradiction."
  | discriminate; zn_log "discriminate."
  | assumption; zn_log "assumption."
  ].

Ltac2 ez_solve () :=
  first
  [ ltac1:(contradiction); zn_log "contradiction."
  | discriminate; zn_log "discriminate."
  | assumption; zn_log "assumption."
  | reflexivity; zn_log "reflexivity."
  | ltac1:(cstring); zn_log "cstring."
  | solve [auto]; zn_log "auto."
  | solve [auto with valid_pointer]; zn_log "auto with valid_pointer."
  | lazy_match! goal with
    | [ |- context [field_compatible] ] => ()
    | [ |- context [field_compatible0] ] => ()
    end; solve [auto with field_compatible]; zn_log "auto with field_compatible."
  | ltac1:(zn_fast_solve)
  ].

Ltac2 norm_plain () :=
  repeat (first
  [ progress (simpl_plain_goal ())
  | progress ltac1:(zn_retry_solve_simpl)
  | progress ltac1:(autorewrite with sublist in * |-); zn_log "autorewrite with sublist in * |-."
  | progress ltac1:(autorewrite with norm sublist); zn_log "autorewrite with norm sublist."
  | progress subst; zn_log "subst."
  ]).

Ltac2 rec finish_plain (fin : unit -> unit) :=
  simpl_plain_goal ();
  try (ez_solve ());
  first
  [ ltac1:(rep_lia); zn_log "rep_lia."
  | ltac1:(cstring'); zn_log "cstring'."
  | ltac1:(Zlength_solve); zn_log "Zlength_solve."
  | ltac1:(computable); zn_log "computable."
  | ltac1:(list_solve); zn_log "list_solve."
  | ltac1:(zn_slow_solve)
  | progress (norm_plain ()); fin ()
  ].

Ltac2 finish_false () :=
  repeat (first
  [ ltac1:(contradiction); zn_log "contradiction."
  | discriminate; zn_log "discriminate."
  | ltac1:(list_solve); zn_log "list_solve."
  | progress subst; zn_log "subst."
  ]).

Ltac inst_EX :=
  repeat lazymatch goal with
  | |- _ |-- ?C =>
    lazymatch C with
    | context [EX x, _] =>
      first
      [ EExists_unify
      | EExists + Exists x
      ]
    end
  end.

Ltac2 simpl_entailer_goal () := Control.enter (fun () =>
  repeat (first
  [ progress ltac1:(Intros); zn_log "Intros."
  | progress ltac1:(simpl_implicit); zn_log "simpl_implicit."
  | progress (subst_decisives ()); zn_log "subst_decisives."
  | progress ltac1:(zn_pre_solve_simpl)
  | lazy_match! goal with
    | [ |- context [if _ then _ else _]] => ltac1:(if_tac); zn_log "if_tac."
    | [ |- context [match ?expr _ with _ => _ end]] => destruct expr > [ | ]; zn_log "destruct match."
    end
  | ltac1:(ex_intros); zn_log "ex_intros."
  | progress ltac1:(inst_EX); zn_log "inst_EX."
  | ltac1:(cstring1); zn_log "cstring1."
  | progress ltac1:(cancel); zn_log "cancel."
  | progress ltac1:(autorewrite with sublist in * |-); zn_log "autorewrite with sublist in * |-."
  | progress ltac1:(autorewrite with sublist); zn_log "autorewrite with sublist."
  | progress ltac1:(autorewrite with norm); zn_log "autorewrite with norm."
  | ltac1:(progress_entailer); zn_log "progress_entailer."
  ])).

Ltac2 norm_entailer () := Control.enter (fun () =>
  repeat (first
  [ progress (simpl_entailer_goal ())
  | progress ltac1:(zn_retry_solve_simpl)
  ])).

Ltac2 rec finish_entailer (fin : unit -> unit) :=
  simpl_entailer_goal ();
  Control.enter (fun () =>
  match! goal with
  | [ |- @derives mpred _ _ _ ] => solve [ltac1:(cancel)]; zn_log "solve [cancel]."
  | [ |- _ |-- _ ] =>
    first
    [ ltac1:(list_solve); zn_log "list_solve."
    | ltac1:(zn_entailer_solve)
    | lazy_match! goal with
      | [ |- context [ _ |-- _ ] ] => progress (norm_entailer ()); finish_entailer fin
      | [ |- _ ] => fin ()
      end
    ]
  | [ |- _ ] => fin ()
  end).

Ltac2 simpl_hyps () := Control.enter (fun () =>
  repeat (
    try (progress (subst_decisives ()); zn_log "subst_decisives.");
    lazy_match! goal with
    | [ h : False |- _ ] =>
      let h := Control.hyp h in
      ltac1:(H |- contradiction H) (Ltac1.of_constr h); zn_log "contradiction H."
    | [ h : _ /\ _ |- _ ] =>
      (* Based on stdpp solution to bug: https://coq.inria.fr/bugs/show_bug.cgi?id=2901 *)
      let h_1 := Fresh.in_goal ident:(H_1) in
      let h_2 := Fresh.in_goal ident:(H_2) in
      destruct h as [h_1 h_2]; try (clear h); zn_log "destruct and in H."
    | [ h : _ \/ _ |- _ ] =>
      let h' := Fresh.in_goal ident:(H') in
      destruct h as [ h' | h' ]; try (clear h); zn_log "destruct or in H."
    | [ h_1 : ?p -> ?q, h_2 : ?p |- _ ] =>
      let h_1 := Control.hyp h_1 in
      let h_2 := Control.hyp h_2 in
      specialize ($h_1 $h_2); zn_log "specialize (H_1 H_2)."
    | [ h : exists _, _ |- _ ] =>
      let x := Fresh.in_goal ident:(x) in
      destruct h as [x hx]; try (clear h); zn_log "destruct exists in H."
    | [ h : andb _ _ = true |- _ ] => rewrite andb_true_iff in h; zn_log "rewrite andb_true_iff in H."
    | [ h : andb _ _ = false |- _ ] => rewrite andb_false_iff in h; zn_log "rewrite andb_false_iff in H."
    | [ h : orb _ _ = true |- _ ] => rewrite orb_true_iff in h; zn_log "rewrite orb_true_iff in H."
    | [ h : orb _ _ = false |- _ ] => rewrite orb_false_iff in h; zn_log "rewrite orb_false_iff in H."
    | [ h : context [Is_true] |- _ ] => rewrite Is_true_eq_true in h; zn_log "rewrite Is_true_eq_true in H."
    | [ |- context [_ |-- _] ] => progress ltac1:(autorewrite with sublist in * |-); zn_log "autorewrite with * |-."
    end
  )).

Global Create HintDb zn_finish.

Ltac2 rec finish_specialize (fin : unit -> unit) := Control.enter (
  fun () => lazy_match! goal with
  | [ |- False ] => finish_false ()
  | [ |- ~ _ ] => unfold not; intros; finish_false ()
  | [ |- _ <-> _ ] => split; zn_log "split."; intro; zn_log "intro."; fin ()
  | [ |- _ /\ _ ] => split; zn_log "split."; fin ()
  | [ |- _ \/ _ ] => zn_log "left + right."; first
    [ left; fin ()
    | right; fin ()
    ]
  | [ |- forall _, _ ] => intro; zn_log "intro."; fin ()
  | [ |- exists _, _ ] => ltac1:(inst_exists); zn_log "inst_exists."; fin ()
  | [ |- ?x = ?x ] => reflexivity; zn_log "reflexivity."
  (* | [ |- context [if _ then _ else _]] => ltac1:(if_tac); zn_log "if_tac."; fin () *) (* TODO: Breaks entailment matching?! Maybe checking nesting? *)
  | [ |- context [match ?expr _ with | _ => _ end]] => destruct expr > [ | ]; zn_log "destruct match."; fin ()
  | [ |- context [_ |-- _] ] => finish_entailer fin
  | [ |- semax _ _ _ _ ] => ltac1:(fail "Semax goal, try 'fastforward' first")
  | [ |- _ ] => first
    [ solve [auto with zn_finish]; zn_log "solve [auto with zn_finish]."
    | finish_plain fin
    ]
  end).

Ltac2 rec finish () :=
  simpl_hyps ();
  finish_specialize finish.

Ltac finish := ltac2:(finish ()).

Ltac2 zsolve (agro : agro_lvl) :=
  progress (
    try (lazy_match! goal with
    | [ |- semax _ _ _ _ ] => fastforward agro
    end);
    try (lazy_match! goal with
    | [ |- semax _ _ _ _ ] => fail
    | [ |- _ ] => finish ()
    end)
  ).

Ltac zsolve := ltac2:(zsolve Safe).
Tactic Notation "zsolve!" := ltac2:(zsolve Med).
Tactic Notation "zsolve!!" := ltac2:(zsolve Slow).

(* A better way to deal with sem_cast_i2bool *)
Lemma sem_cast_i2bool_of_bool : forall (b : bool),
  sem_cast_i2bool (Val.of_bool b) = Some (Val.of_bool b).
Proof.
  destruct b; auto.
Qed.
(*after Coq 8.13: #[export]*) Hint Rewrite sem_cast_i2bool_of_bool : norm.

#[export] Hint Extern 1 (@eq Z _ _) => Zlength_solve : Zlength_solve.
#[export] Hint Extern 1 (@eq _ _ _) => f_equal : f_equal.

Lemma computable_sizeof: forall cs x, computable x -> computable (@sizeof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_sizeof : computable.

Lemma computable_Ctypes_sizeof: forall cs x, computable x -> computable (@Ctypes.sizeof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Ctypes_sizeof : computable.

Lemma computable_alignof: forall cs x, computable x -> computable (@alignof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_alignof : computable.

Lemma computable_Ctypes_alignof: forall cs x, computable x -> computable (@Ctypes.alignof cs x).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Ctypes_alignof : computable.

Lemma computable_Tint: forall sz s a, computable (Tint sz s a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tint : computable.

Lemma computable_Tlong: forall s a, computable (Tlong s a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tlong : computable.

Lemma computable_Tarray: forall t i a, computable t -> computable i -> computable (Tarray t i a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tarray : computable.

Lemma computable_Tstruct: forall i a, computable i -> computable (Tstruct i a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tstruct : computable.

Lemma computable_Tunion: forall i a, computable i -> computable (Tunion i a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tunion : computable.

Lemma computable_Tpointer: forall t a, computable t -> computable (Tpointer t a).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_Tpointer : computable.

Lemma computable_tptr: forall t, computable t -> computable (tptr t).
Proof. intros. apply computable_any. Qed.
#[export] Hint Resolve computable_tptr : computable.


(* a little bit of profiling infrastructure . . .
Tactic Notation "entailer" "!" := time "ent2" entbang.
Ltac entailer := time "ent1" floyd.entailer.entailer.
*)

Ltac gather_prop ::=
(* autorewrite with gather_prop_core;  (* faster to do this first *)*)
 autorewrite with gather_prop.

#[export] Hint Resolve Clight_mapsto_memory_block.tc_val_pointer_nullval : core.
#[export] Hint Resolve mapsto_memory_block.tc_val_pointer_nullval : core.

(*
Ltac eapply_clean_LOCAL_right_spec'' R ::=
  lazymatch R with
  | context [@data_at ?CS _ _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | context [@field_at ?CS _ _ _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | context [@data_at_ ?CS _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | context [@field_at_ ?CS _ _ _ _] => eapply_clean_LOCAL_right_spec' CS
  | _ => 
  match R with context [?CS] => 
     lazymatch type of CS with compspecs =>
       eapply_clean_LOCAL_right_spec' CS || fail 1
     end
  | _ => eapply_clean_LOCAL_right_spec' emptyCS
  end
 end.

Ltac eapply_clean_LOCAL_right_spec'' R :=
   eapply_clean_LOCAL_right_spec' emptyCS.
*)


