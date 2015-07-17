Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Export veric.lift.
Require Export veric.Cop2.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.res_predicates.
Require Import veric.extend_tc.
Require Import veric.seplog.

Inductive rel_expr' (Delta: tycontext) (rho: environ) (phi: rmap): expr -> val -> Prop :=
 | rel_expr'_const_int: forall i ty, 
                 rel_expr' Delta rho phi (Econst_int i ty) (Vint i)
 | rel_expr'_const_float: forall f ty, 
                 rel_expr' Delta rho phi (Econst_float f ty) (Vfloat f)
 | rel_expr'_const_single: forall f ty, 
                 rel_expr' Delta rho phi (Econst_single f ty) (Vsingle f)
 | rel_expr'_const_long: forall i ty, 
                 rel_expr' Delta rho phi (Econst_long i ty) (Vlong i)
 | rel_expr'_tempvar: forall id ty v,
                 Map.get (te_of rho) id = Some v ->
                 rel_expr' Delta rho phi (Etempvar id ty) v
 | rel_expr'_addrof: forall a ty v,
                 rel_lvalue' Delta rho phi a v ->
                 rel_expr' Delta rho phi (Eaddrof a ty) v
 | rel_expr'_unop: forall a v1 v ty op,
                 rel_expr' Delta rho phi a v1 ->
                 Cop.sem_unary_operation op v1 (typeof a) = Some v ->
                 rel_expr' Delta rho phi (Eunop op a ty) v
 | rel_expr'_binop: forall a1 a2 v1 v2 v ty op,
                 rel_expr' Delta rho phi a1 v1 ->
                 rel_expr' Delta rho phi a2 v2 ->
                 binop_stable (composite_types Delta) op a1 a2 = true ->
                 (forall m, Cop.sem_binary_operation (composite_types Delta) op v1 (typeof a1) v2 (typeof a2) m = Some v) ->
                 rel_expr' Delta rho phi (Ebinop op a1 a2 ty) v
 | rel_expr'_cast: forall a v1 v ty,
                 rel_expr' Delta rho phi a v1 ->
                 Cop.sem_cast v1 (typeof a) ty = Some v ->
                 rel_expr' Delta rho phi (Ecast a ty) v
 | rel_expr'_sizeof: forall t ty,
                 complete_type (composite_types Delta) t = true ->
                 rel_expr' Delta rho phi (Esizeof t ty) (Vint (Int.repr (sizeof (composite_types Delta) t)))
 | rel_expr'_alignof: forall t ty,
                 complete_type (composite_types Delta) t = true ->
                 rel_expr' Delta rho phi (Ealignof t ty) (Vint (Int.repr (alignof (composite_types Delta) t)))
 | rel_expr'_lvalue_By_value: forall a ch sh v1 v2,
                 access_mode (typeof a) = By_value ch ->
                 rel_lvalue' Delta rho phi a v1 ->
                 app_pred (mapsto sh (typeof a) v1 v2 * TT ) phi ->
                 v2 <> Vundef ->
                 rel_expr' Delta rho phi a v2
 | rel_expr'_lvalue_By_reference: forall a v1,
                 access_mode (typeof a) = By_reference ->
                 rel_lvalue' Delta rho phi a v1 ->
                 rel_expr' Delta rho phi a v1
with rel_lvalue' (Delta: tycontext) (rho: environ) (phi: rmap): expr -> val -> Prop :=
 | rel_expr'_local: forall id ty b,
                 Map.get (ve_of rho) id = Some (b,ty) ->
                 rel_lvalue' Delta rho phi (Evar id ty) (Vptr  b Int.zero)
 | rel_expr'_global: forall id ty b,
                 Map.get (ve_of rho) id = None ->
                 Map.get (ge_of rho) id = Some b ->
                 rel_lvalue' Delta rho phi (Evar id ty) (Vptr b Int.zero)
 | rel_lvalue'_deref: forall a b z ty,
                 rel_expr' Delta rho phi a (Vptr b z) ->
                 rel_lvalue' Delta rho phi (Ederef a ty) (Vptr b z)
 | rel_lvalue'_field_struct: forall i ty a b z id co att delta,
                 rel_expr' Delta rho phi a (Vptr b z) ->
                 typeof a = Tstruct id att ->
                 (composite_types Delta) ! id = Some co ->
                 field_offset (composite_types Delta) i (co_members co) = Errors.OK delta ->
                 rel_lvalue' Delta rho phi (Efield a i ty) (Vptr b (Int.add z (Int.repr delta))).

Scheme rel_expr'_sch := Minimality for rel_expr' Sort Prop
  with rel_lvalue'_sch := Minimality for  rel_lvalue' Sort Prop.

Lemma rel_expr'_hered: forall Delta e v rho, hereditary age (fun phi => rel_expr' Delta rho phi e v).
Proof.
intros.
intro; intros.
apply (rel_expr'_sch Delta rho a (rel_expr' Delta rho a') (rel_lvalue' Delta rho a'));
  intros;
  try solve [econstructor; eauto].
  eapply rel_expr'_lvalue_By_value; eauto.
  eapply pred_hereditary; eassumption.
  eapply rel_expr'_lvalue_By_reference; eauto.
 constructor 2; auto.
  auto.
Qed.

Lemma rel_lvalue'_hered: forall Delta e v rho, hereditary age (fun phi => rel_lvalue' Delta rho phi e v).
Proof.
intros.
intro; intros.
induction H0; try solve [ econstructor; eauto].
 constructor 2; auto.
 constructor 3; auto.
apply rel_expr'_hered with a; auto.
  econstructor 4; eauto.
apply rel_expr'_hered with a; auto.
Qed.

Program Definition rel_expr (Delta: tycontext) (e: expr) (v: val) (rho: environ) : pred rmap :=
    fun phi => rel_expr' Delta rho phi e v.
Next Obligation. intros. apply rel_expr'_hered. Defined.

Program Definition rel_lvalue (Delta: tycontext) (e: expr) (v: val) (rho: environ) : pred rmap :=
    fun phi => rel_lvalue' Delta rho phi e v.
Next Obligation. intros. apply rel_lvalue'_hered. Defined.

Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.expr_lemmas.

Definition rel_lvalue'_expr'_sch Delta rho phi P P0 :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  conj (rel_expr'_sch Delta rho phi P P0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
       (rel_lvalue'_sch Delta rho phi P P0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).

Lemma rel_lvalue_expr_relate:
  forall Delta ge te ve rho jm,
    guard_genv Delta ge ->
    rho = construct_rho (filter_genv ge) ve te ->
    (forall e v,
           rel_expr Delta e v rho (m_phi jm) ->
           Clight.eval_expr ge ve te (m_dry jm) e v) /\
    (forall e v,
           rel_lvalue Delta e v rho (m_phi jm) ->
           match v with
           | Vptr b z => Clight.eval_lvalue ge ve te (m_dry jm) e b z
           | _ => False
           end).
Proof.
intros.
unfold rel_expr, rel_lvalue.
simpl.
apply (rel_lvalue'_expr'_sch Delta rho (m_phi jm)
     (Clight.eval_expr ge ve te (m_dry jm))
     (fun e v =>
      match v with
      | Vptr b z => Clight.eval_lvalue ge ve te (m_dry jm) e b z
      | _ => False end));
 intros; subst rho; try solve [econstructor; eauto].
* (* Eaddrof *)
   destruct v; try contradiction. constructor; auto.
* (* Ebinop *)
  econstructor; eauto.
  erewrite <- Cop_sem_binary_operation_guard_genv; eauto.
* (* Esizeof *)
  erewrite sizeof_guard_genv by eauto.
  constructor.
* (* Ealignof *)
  erewrite alignof_guard_genv by eauto.
  constructor.
* (* lvalue *)
  destruct v1; try contradiction.
  eapply Clight.eval_Elvalue; eauto.
  destruct H4 as [m1 [m2 [? [? _]]]].
  unfold mapsto in H4.
  rewrite H1 in *.
  destruct (type_is_volatile (typeof a)) eqn:?; try contradiction.
  eapply deref_loc_value; try eassumption.
  unfold Mem.loadv.
  destruct H4 as [[_ ?] | [? _]]; [ | contradiction].
  apply core_load_load'.
  destruct H4 as [bl ?]; exists bl.
  destruct H4 as [H3' ?]; split; auto.
  clear H3'. 
  intro b'; specialize (H4 b'). hnf in H4|-*.
  if_tac; auto. destruct H4 as [p ?].
  hnf in H4. rewrite preds_fmap_NoneP in H4.
  apply (resource_at_join _ _ _ b') in H0.  
  rewrite H4 in H0; clear H4.
  inv H0.
  symmetry in H12.
  exists rsh3, (Share.unrel Share.Rsh sh), p; assumption.
  symmetry in H12.
  simpl.
  destruct sh3 as [sh3 p3].  exists rsh3, sh3, p3; auto.
 apply I.
* (* lvalue By_reference *)
   destruct v1; try contradiction.
  eapply Clight.eval_Elvalue; eauto.
    eapply deref_loc_reference; try eassumption.
* (* Evar *)
  simpl in *.
  unfold Map.get, make_venv, filter_genv in H1,H2.
  destruct (Genv.find_symbol ge id) eqn:?; try discriminate.
  destruct (type_of_global ge b) eqn:?; inv H2;  apply Clight.eval_Evar_global; auto.
* (* Efield *)
  econstructor; eauto.
  + eapply guard_genv_spec; eauto.
  + eapply field_offset_guard_genv; eauto.
Qed.

Lemma rel_expr_relate:
  forall Delta ge te ve rho e jm v,
           guard_genv Delta ge ->
           rho = construct_rho (filter_genv ge) ve te ->
           rel_expr Delta e v rho (m_phi jm) ->
           Clight.eval_expr ge ve te (m_dry jm) e v.
Proof.
  intros.
  apply (proj1 (rel_lvalue_expr_relate Delta ge te ve rho jm H H0)).
  auto.
Qed.

Lemma rel_lvalue_relate:
  forall Delta ge te ve rho e jm b z,
           guard_genv Delta ge ->
           rho = construct_rho (filter_genv ge) ve te ->
           rel_lvalue Delta e (Vptr b z) rho (m_phi jm) ->
           Clight.eval_lvalue ge ve te (m_dry jm) e b z.
Proof.
  intros.
  apply ((proj2 (rel_lvalue_expr_relate Delta ge te ve rho jm H H0)) e (Vptr b z)).
  auto.
Qed.

Lemma sem_cast_load_result:
 forall v1 t1 t2 v2 ch,
  access_mode t1 = By_value ch ->
(*  Clight.eval_expr ge ve te m e2 v1 -> *)
   Cop.sem_cast v1 t2 t1 = Some v2 ->
  Val.load_result ch v2 = v2.
Proof.
intros.
unfold Cop.sem_cast in H0.

destruct t1 as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
destruct t2 as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
inv H; try reflexivity;
 simpl in H0; try discriminate;
 destruct v1; inv H0;
  try invSome;
 simpl;
 try  rewrite Int.sign_ext_idem by omega;
 try  rewrite Int.zero_ext_idem by omega;
 try reflexivity;
 try match goal with
 | |- context [Int.eq ?i Int.zero] =>
  destruct (Int.eq i Int.zero) eqn:?; try reflexivity
 | |- context [Int64.eq ?i Int64.zero] =>
  destruct (Int64.eq i Int64.zero) eqn:?; try reflexivity
 | |- context [Float.cmp Ceq ?f Float.zero] =>
     destruct (Float.cmp Ceq f Float.zero) eqn:?; try reflexivity
 | |- context [Float32.cmp Ceq ?f Float32.zero] =>
     destruct (Float32.cmp Ceq f Float32.zero) eqn:?; try reflexivity
 end.
Qed.

Lemma deref_loc_load_result:
  forall t ch m loc ofs v2,
  access_mode t = By_value ch ->
  deref_loc t m loc ofs v2 ->
  Val.load_result ch v2 = v2.
Proof.
intros.
destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 inv H0; inversion2 H H1; inv H; unfold Mem.loadv in *;
 apply Mem.load_result in H2; subst; simpl;
 match goal with 
  | |- context [decode_val _ (?x :: nil)] => destruct x; try reflexivity
  | |- context [decode_val _ (?x :: ?y :: nil)] => destruct x,y; try reflexivity
  | |- context [decode_val ?ch ?a] => destruct (decode_val ch a) eqn:?; try reflexivity
  | |- _ => idtac
 end;
  simpl;
  try rewrite Int.sign_ext_idem by omega;
  try rewrite Int.zero_ext_idem by omega;
  try reflexivity;
 try match type of Heqv with
  | decode_val _ (?a :: ?b :: ?c :: ?d :: nil) = _ =>
    destruct a; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct b; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct c; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct d; try solve [unfold decode_val in Heqv; inv Heqv];
   unfold decode_val in Heqv; inv Heqv;
  try (if_tac in H0; inv H0)
 | decode_val _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?g :: ?h :: nil) = _ =>
    destruct a; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct b; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct c; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct d; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct e; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct f; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct g; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct h; try solve [unfold decode_val in Heqv; inv Heqv]
 end;
 try solve [destruct v; inv H1; auto].
Qed.

Lemma rel_expr'_fun:
 forall Delta rho phi e v v', rel_expr' Delta rho phi e v -> rel_expr' Delta rho phi e v' -> v=v'.
Proof.
intros until 1.
apply (rel_expr'_sch Delta rho phi
      (fun e v => forall v', rel_expr' Delta rho phi e v -> rel_expr' Delta rho phi e v' -> v=v')
      (fun e v => forall v', rel_lvalue' Delta rho phi e v -> rel_lvalue' Delta rho phi e v' -> v=v'));
   auto; intros;
   try match goal with H : _ |- _ => inv H; auto; try congruence end;
   try match goal with H: rel_lvalue' _ _ _ _ _ |- _ => solve [inv H] end.
* (* Eunop *)
   specialize (H1 _ H0 H9). congruence.
* (* Ebinnop *)
   specialize (H1 _ H0 H12). specialize (H3 _ H2 H14).
   specialize (H5 Mem.empty). specialize (H16 Mem.empty).
   congruence.
* (* Ecast *)
   specialize (H1 _ H0 H7). congruence.
*
   inversion2 H0 H7.
   specialize (H2 _ H1 H8).
   subst v0.   clear H1 H8.
   generalize H3; intros [wx [wy [_ [? _]]]].
   unfold mapsto in *.
   destruct (access_mode (typeof a)); try contradiction.
   destruct (type_is_volatile (typeof a)); try contradiction.
   destruct v1; try contradiction.
   destruct H1 as [[? ?]|[? ?]]; [ |  hnf in H1; contradiction].
   clear H2.
   rewrite distrib_orp_sepcon in H3,H9.
   destruct H3 as [H3|[? [? [? [[Hx _] _]]]]]; [ | hnf in Hx; contradiction].
   destruct H9 as [H9|[? [? [? [[Hx _] _]]]]]; [ | hnf in Hx; contradiction].
   autorewrite with normalize in H3,H9; auto with typeclass_instances.
   destruct H9 .
   eapply res_predicates.address_mapsto_fun; split; eauto.
*
   specialize (H1 _ H0 H10). congruence.
Qed.

Lemma rel_expr_extend:
  forall Delta e v rho, boxy extendM (rel_expr Delta e v rho).
Proof.
intros. apply boxy_i; intros; auto.
hnf in H0|-*.
apply (rel_expr'_sch Delta rho w
      (fun e v => rel_expr' Delta rho w e v -> rel_expr' Delta rho w' e v)
      (fun e v => rel_lvalue' Delta rho w e v -> rel_lvalue' Delta rho w' e v)); auto; intros;
 try solve [match goal with H : _ |- _ => inv H; econstructor; eauto end].
*
eapply rel_expr'_lvalue_By_value; eauto.
instantiate (1:=sh).
destruct H as [w1 ?].
destruct H4 as [w3 [w4 [? [? _]]]].
destruct (join_assoc H4 H) as [w6 [? ?]].
exists w3, w6; split3; auto.
*
eapply rel_expr'_lvalue_By_reference; eauto.
*
econstructor 2; eauto.
*
inv H6.
pose proof (rel_expr'_fun _ _ _ _ _ _ H1 H12). inv H6.
rewrite H3 in H13. symmetry in H13; inv H13.
rewrite H4 in H14. symmetry in H14; inv H14.
rewrite H5 in H15; symmetry in H15; inv H15.
econstructor; eauto.
Qed.

Lemma rel_lvalue_extend:
  forall Delta e v rho, boxy extendM (rel_lvalue Delta e v rho).
Proof.
intros. apply boxy_i; intros; auto.
hnf in H0|-*.
inv H0; try solve [econstructor; eauto].
econstructor 2; eauto.
econstructor; eauto.
pose proof (rel_expr_extend Delta a (Vptr b z) rho).
apply (boxy_e _ _ H0 _ _ H); auto.
econstructor; eauto.
apply (boxy_e _ _ (rel_expr_extend Delta a (Vptr b z) rho) _ _ H); auto.
Qed.

Section TYCON_SUB.
Variables Delta Delta': tycontext.
Hypothesis extends: tycontext_sub Delta Delta'.

Lemma rel_lvalue_expr_sub:
  forall rho phi,
  (forall e v, rel_expr' Delta rho phi e v -> rel_expr' Delta' rho phi e v) /\  
  (forall e v, rel_lvalue' Delta rho phi e v -> rel_lvalue' Delta' rho phi e v).
Proof.
  intros.
  apply (rel_lvalue'_expr'_sch Delta rho phi
     (rel_expr' Delta' rho phi)
     (rel_lvalue' Delta' rho phi));
  intros; try solve [econstructor; eauto].
  + (* Ebinop *)
    econstructor; eauto.
    - eapply binop_stable_sub; eauto.
    - intro m; specialize (H4 m).
      erewrite <- Cop_sem_binary_operation_sub; eauto.
  + (* Esizeof *)
    erewrite sizeof_sub by eauto.
    econstructor; eauto.
    eapply complete_type_sub; eauto.
  + (* Ealignof *)
    erewrite alignof_sub by eauto.
    econstructor; eauto.
    eapply complete_type_sub; eauto.
  + (* lvalue By_reference *)
    apply rel_expr'_lvalue_By_reference; auto.
  + (* global *)
    apply rel_expr'_global; auto.
  + (* Struct Field *)
    eapply rel_lvalue'_field_struct; eauto.
    - eapply composite_types_get_sub; eauto.
    - eapply field_offset_sub; eauto.
Qed.

Lemma rel_lvalue_sub: forall rho e v, rel_lvalue Delta e v rho |-- rel_lvalue Delta' e v rho.
Proof.
  intros.
  intro w.
  eapply (proj2 (rel_lvalue_expr_sub rho w) e v).
Qed.

Lemma rel_expr_sub: forall rho e v, rel_expr Delta e v rho |-- rel_expr Delta' e v rho.
Proof.
  intros.
  intro w.
  eapply (proj1 (rel_lvalue_expr_sub rho w) e v).
Qed.

End TYCON_SUB.

