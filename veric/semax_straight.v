Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.semax_conseq.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.binop_lemmas.
Require Import VST.veric.binop_lemmas4.
Local Open Scope pred.
Import LiftNotation.
Import compcert.lib.Maps.

Transparent intsize_eq.

Section extensions.
  Context {CS: compspecs} {Espec: OracleKind}.

Lemma semax_straight_simple:
 forall Delta (B: assert) P c Q,
  (forall rho, boxy (@extendM rmap _ _ _ _ _ _ rmap _ _ _ _ _) (B rho)) ->
  (forall jm jm1 Delta' ge ve te rho k F f,
              tycontext_sub Delta Delta' ->
              app_pred (B rho) (m_phi jm) ->
              guard_environ Delta' f rho ->
              closed_wrt_modvars c F ->
              rho = construct_rho (filter_genv ge) ve te  ->
              age jm jm1 ->
              ((F rho * |>P rho) && funassert Delta' rho) (m_phi jm) ->
              (*genv_cenv ge = cenv_cs*) cenv_sub cenv_cs (genv_cenv ge) ->
              exists jm', exists te', exists rho',
                rho' = mkEnviron (ge_of rho) (ve_of rho) (make_tenv te') /\
                level jm = S (level jm') /\
                guard_environ Delta' f rho'  /\
                jstep (cl_core_sem ge) (State f c k ve te) jm
                                 (State f Sskip k ve te') jm' /\
              ((F rho' * Q rho') && funassert Delta' rho) (m_phi jm')) ->
  semax Espec Delta (fun rho => B rho && |> P rho) c (normal_ret_assert Q).
Proof.
intros until Q; intros EB Hc.
rewrite semax_unfold.
intros psi Delta' CS' n TS [CSUB HGG'] _ k F f Hcl Hsafe te ve w Hx ? w0 H Hext Hglob.
specialize (cenv_sub_trans CSUB HGG'); intros HGG.
apply nec_nat in Hx.
apply (pred_nec_hereditary _ _ _ Hx) in Hsafe.
clear n Hx.
apply (pred_nec_hereditary _ _ _ (necR_nat H)) in Hsafe.
clear H w.
rename w0 into w.
apply assert_safe_last'; intro Hage.
apply own.bupd_intro.
intros ora jm Hora _ H2. subst w.
destruct Hglob as [[TC' Hglob] Hglob'].
apply can_age_jm in Hage; destruct Hage as [jm1 Hage].
apply extend_sepcon_andp in Hglob; auto.
destruct Hglob as [TC2 Hglob].
specialize (Hc jm jm1 Delta' psi ve te _ k F f TS TC2 TC' Hcl (eq_refl _) Hage).
specialize (Hc (conj Hglob Hglob') HGG); clear Hglob Hglob'.
destruct Hc as [jm' [te' [rho' [H9 [H2 [TC'' [H3 H4]]]]]]].
change (@level rmap _  (m_phi jm) = S (level (m_phi jm'))) in H2.
apply rmap_order in Hext as (Hl & Hr & _); rewrite Hl in *.
rewrite H2 in Hsafe.
rewrite <- level_juice_level_phi, (age_level _ _ Hage).
econstructor; [eassumption | ].
unfold rguard in Hsafe.
specialize (Hsafe EK_normal None te' ve).
simpl exit_cont in Hsafe.
specialize (Hsafe (m_phi jm')).
spec Hsafe.
change R.rmap with rmap; lia.
specialize (Hsafe _ _ (necR_refl _) (ext_refl _)).
destruct H4.
spec Hsafe; [clear Hsafe| ].
split; auto.
simpl proj_ret_assert.
rewrite (prop_true_andp (None=None)) by auto.
split; auto.
subst rho'; auto.
rewrite sepcon_comm; subst rho'; auto.
subst rho'.
replace (level jm1) with (level jm').
simpl exit_cont in Hsafe.
apply assert_safe_jsafe'; auto.
rewrite <- !level_juice_level_phi in H2.
apply age_level in Hage; lia.
Qed.

Definition force_valid_pointers m v1 v2 :=
match v1, v2 with
| Vptr b1 ofs1, Vptr b2 ofs2 =>
    (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
    Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2))%bool
| _, _ => false
end.

Definition blocks_match op v1 v2 :=
match op with Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge =>
  match v1, v2 with
    Vptr b _, Vptr b2 _ => b=b2
    | _, _ => False
  end
| _ => True
end.

Lemma later_sepcon2  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
  forall P Q,  P * |> Q |-- |> (P * Q).
Proof.
intros. apply @derives_trans with (|> P * |> Q).
apply sepcon_derives; auto. rewrite later_sepcon; auto.
Qed.


Lemma perm_order''_trans:
  forall x y z, perm_order'' x y -> perm_order'' y z -> perm_order'' x z.
Proof.
intros.
destruct x,y; inv H; auto.
destruct z; constructor.
destruct z; inv H0; constructor.
destruct z; inv H0; constructor.
destruct z; inv H0; constructor.
Qed.

Lemma mapsto_valid_pointer : forall b o sh t jm,
 nonidentity sh ->
(mapsto_ sh (t) (Vptr b o) * TT)%pred (m_phi jm) ->
Mem.valid_pointer (m_dry jm) b (Ptrofs.unsigned o) = true.
intros. rename H into N.

destruct H0. destruct H. destruct H. destruct H0.
unfold mapsto_,mapsto in H0.  unfold mapsto in *.
destruct (readable_share_dec sh) as [H2 | H2].
* (* readable_share sh *)
rename H2 into RS.
destruct (access_mode t); try solve [ inv H0].
destruct (type_is_volatile t) eqn:VOL; try contradiction.
assert (exists v,  address_mapsto m v sh (b, Ptrofs.unsigned o) x).
destruct H0.
econstructor; apply H0. destruct H0 as [_ [v2' H0]]; exists v2'; apply H0.
clear H0; destruct H2 as [x1 H0].

pose proof mapsto_core_load m x1 sh (b, Ptrofs.unsigned o) (m_phi jm).

destruct H2. simpl; eauto.
simpl in H2.
destruct H2.
specialize (H3 (b, Ptrofs.unsigned o)).
if_tac in H3.
destruct H3.  destruct H3.

rewrite valid_pointer_nonempty_perm.
unfold perm.

assert (JMA := juicy_mem_access jm (b, Ptrofs.unsigned o)).
unfold access_at in *. simpl in JMA.
unfold perm_of_res in *.
rewrite H3 in JMA. simpl in JMA.
unfold perm_of_sh in *.
rewrite JMA.
repeat if_tac; try constructor. subst.
simpl in H3.
contradiction.
destruct H4.  repeat split. lia.
destruct m; simpl; lia.
* (* ~ readable_share sh *)
destruct (access_mode t) eqn:?; try contradiction.
destruct (type_is_volatile t); [inversion H0 |].
destruct H0 as [_ ?].
specialize (H0 (b, Ptrofs.unsigned o)).
simpl in H0.
rewrite if_true in H0
 by (split; auto; pose proof (size_chunk_pos m); lia).
clear H1.
pose proof (resource_at_join _ _ _ (b, Ptrofs.unsigned o) H).
unfold resource_share in H0.
rewrite <- (Z.add_0_r (Ptrofs.unsigned o)).
apply (valid_pointer_dry b o 0 jm).
hnf.
rewrite Z.add_0_r.
destruct H0.
destruct  (x @ (b, Ptrofs.unsigned o)); inv H0; inv H1; simpl; auto.
intro.
apply split_identity in RJ; auto.
Qed.

Lemma mapsto_is_pointer : forall sh t m v,
mapsto_ sh t v m ->
exists b, exists o, v = Vptr b o.
Proof.
intros. unfold mapsto_, mapsto in H.
if_tac in H; try contradiction;
destruct (access_mode t); try contradiction;
destruct (type_is_volatile t); try contradiction.
destruct v; try contradiction.
eauto.
destruct v; try contradiction.
eauto.
Qed.

Lemma pointer_cmp_eval:
  forall (Delta : tycontext) (cmp : Cop.binary_operation) (e1 e2 : expr) sh1 sh2 ge
         (GE: cenv_sub cenv_cs (genv_cenv ge)),
   is_comparison cmp = true ->
   forall (jm : juicy_mem) (rho : environ),
   (tc_expr Delta e1 rho) (m_phi jm) ->
   (tc_expr Delta e2 rho) (m_phi jm) ->
   blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho) ->
   typecheck_environ Delta rho ->
   nonidentity sh1 ->
   nonidentity sh2 ->
   (mapsto_ sh1 (typeof e1) (eval_expr e1 rho) * TT)%pred (m_phi jm) ->
   (mapsto_ sh2 (typeof e2) (eval_expr e2 rho) * TT)%pred (m_phi jm) ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   Cop.sem_binary_operation (*cenv_cs*)ge cmp (eval_expr e1 rho)
     (typeof e1) (eval_expr e2 rho) (typeof e2) (m_dry jm) =
  Some
     (force_val
        (sem_binary_operation' cmp (typeof e1) (typeof e2)
           (eval_expr e1 rho) (eval_expr e2 rho))).
Proof.
intros until rho. intros ? ? BM ? N1 N2 ? ? NE1 NE2.
unfold Cop.sem_binary_operation, sem_cmp.
simpl in H0, H1. apply typecheck_expr_sound in H0; auto.
apply typecheck_expr_sound in H1; auto.

copy H3. copy H4. rename H5 into MT_1.
rename H6 into MT_2.
destruct H3 as [? [? [J1 [MT1 _]]]].
destruct H4 as [? [? [J2 [MT2 _]]]].
destruct (mapsto_is_pointer _ _ _ _ MT1) as [? [? ?]].
destruct (mapsto_is_pointer _ _ _ _ MT2) as [? [? ?]].

unfold blocks_match in *.
simpl in BM.

rewrite H3 in *. rewrite H4 in *.
apply mapsto_valid_pointer in MT_1; auto.
apply mapsto_valid_pointer in MT_2; auto.
forget (typeof e1) as t1.
forget (typeof e2) as t2.
clear e1 e2 H3 H4.
unfold Cop.sem_cmp, Cop.sem_binarith; simpl.
unfold  cmp_ptr, Val.cmpu_bool, Val.cmplu_bool.
rewrite MT_1, MT_2.
simpl.
clear MT_1 MT_2.
unfold mapsto_ in MT1, MT2.
unfold mapsto in MT1,MT2.
destruct (access_mode t1) eqn:?A1;
 try solve [simpl in MT1; contradiction].
destruct (access_mode t2) eqn:?A2;
 try solve [simpl in MT2; contradiction].
clear MT1 MT2.
destruct t1; try solve [simpl in *; try destruct f; try tauto; congruence].
destruct t2; try solve [simpl in *; try destruct f; try tauto; congruence].
simpl.
unfold sem_binary_operation', sem_cmp.
rewrite NE1,NE2.
destruct cmp;
inv H; subst; simpl;
unfold Cop.sem_cmp, sem_cmp_pp, cmp_ptr, Val.cmpu_bool, Val.cmplu_bool; simpl;
try rewrite MT_1; try rewrite MT_2; simpl;
destruct Archi.ptr64  eqn:Hp;
try rewrite if_true by auto;
try solve[if_tac; subst; eauto]; try repeat rewrite peq_true; eauto.
all: simpl; destruct (eq_block x3 x5); try reflexivity.
Qed.

Lemma is_int_of_bool:
  forall i s b, is_int i s (Val.of_bool b).
Proof.
Transparent Int.repr.
destruct i,s,b; simpl; auto;
compute; try split; congruence.
Opaque Int.repr.
Qed.

Lemma pointer_cmp_no_mem_bool_type:
   forall (Delta : tycontext) cmp (e1 e2 : expr) sh1 sh2 x1 x b1 o1 b2 o2 i3 s3,
   is_comparison cmp = true->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   forall (rho : environ) phi,
   eval_expr e1 rho = Vptr b1 o1 ->
   eval_expr e2 rho = Vptr b2 o2 ->
   blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho) ->
   denote_tc_assert (typecheck_expr Delta e1) rho phi ->
   denote_tc_assert (typecheck_expr Delta e2) rho phi ->
   (mapsto_ sh1 (typeof e1)
      (eval_expr e1 rho)) x ->
   (mapsto_ sh2 (typeof e2)
      (eval_expr e2 rho)) x1 ->
   typecheck_environ Delta rho ->
    is_int i3 s3
     (force_val
        (sem_binary_operation' cmp (typeof e1) (typeof e2)
           (eval_expr e1 rho)
           (eval_expr e2 rho))).
Proof.
intros until 1. intros NE1 NE2; intros.
apply typecheck_both_sound in H4; auto.
apply typecheck_both_sound in H3; auto.
rewrite H0 in *.
rewrite H1 in *.
unfold sem_binary_operation'.
forget (typeof e1) as t1.
forget (typeof e2) as t2.
clear e1 e2 H0 H1.
unfold mapsto_ in *.
unfold mapsto in *.
destruct (access_mode t1) eqn:?A1;
 try solve [simpl in H5; contradiction].
destruct (access_mode t2) eqn:?A2;
 try solve [simpl in H6; contradiction].
destruct t1 as [ | | | [ | ] | | | | | ]; try solve[simpl in *; try contradiction; try congruence];
destruct t2 as [ | | | [ | ] | | | | | ]; try solve[simpl in *; try contradiction; try congruence].
unfold sem_cmp, sem_cmp_pp, cmp_ptr, Val.cmpu_bool, Val.cmplu_bool.
rewrite NE1,NE2.
destruct Archi.ptr64 eqn:Hp;
destruct cmp; inv H;
unfold sem_cmp; simpl;
if_tac; auto; simpl; try of_bool_destruct; auto;
try apply is_int_of_bool.

Transparent Int.repr.
all: destruct i3,s3; simpl; auto; compute; try split; congruence.
Opaque Int.repr.
Qed.

Definition weak_mapsto_ sh e rho :=
match (eval_expr e rho) with
| Vptr b o => (mapsto_ sh (typeof e) (Vptr b o)) ||
              (mapsto_ sh (typeof e) (Vptr b o))
| _ => FF
end.

Lemma extend_sepcon_TT {A} {JA: Join A} {PA: Perm_alg A}{SA: Sep_alg A} {AG: ageable A} {Aga: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
 forall P, boxy extendM (P * TT).
Proof. intros. hnf.
 apply pred_ext.
 intros ? ?. hnf in H. apply H. apply extendM_refl.
 intros ? ?. intros ? ?. destruct H0 as [b ?].
 destruct H as [? [? [? [? ?]]]].
 destruct (join_assoc H H0) as [c [? ?]].
 exists x; exists c; split; auto.
Qed.

Lemma semax_ptr_compare:
forall (Delta: tycontext) (P: assert) id cmp e1 e2 ty sh1 sh2,
    nonidentity sh1 -> nonidentity sh2 ->
    is_comparison cmp = true  ->
     eqb_type (typeof e1) int_or_ptr_type = false ->
    eqb_type (typeof e2) int_or_ptr_type = false ->
    (typecheck_tid_ptr_compare Delta id = true) ->
    semax Espec Delta
        (fun rho =>
          |> (tc_expr Delta e1 rho && tc_expr Delta e2 rho  &&

          !!(blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho)) &&
          (mapsto_ sh1 (typeof e1) (eval_expr e1 rho) * TT) &&
          (mapsto_ sh2 (typeof e2) (eval_expr e2 rho) * TT) &&
          P rho))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (fun rho => (EX old:val,
                 !!(eval_id id rho =  subst id (`old)
                     (eval_expr (Ebinop cmp e1 e2 ty)) rho) &&
                            subst id (`old) P rho))).
Proof.
  intros until sh2. intros N1 N2. intros ? NE1 NE2. revert H.
  replace (fun rho : environ =>
     |> (tc_expr Delta e1 rho && tc_expr Delta e2 rho  &&
             !!blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho) &&
            (mapsto_ sh1 (typeof e1) (eval_expr e1 rho) * TT) &&
            (mapsto_ sh2 (typeof e2) (eval_expr e2 rho) * TT) &&
            P rho))
    with (fun rho : environ =>
       (|> tc_expr Delta e1 rho &&
        |> tc_expr Delta e2 rho &&
        |> !!blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho) &&
        |> (mapsto_ sh1 (typeof e1) (eval_expr e1 rho) * TT) &&
        |> (mapsto_ sh2 (typeof e2) (eval_expr e2 rho) * TT) &&
        |> P rho))
    by (extensionality rho;  repeat rewrite later_andp; auto).
  intros CMP TC2.
  apply semax_straight_simple; auto.
  intros; repeat apply boxy_andp; auto;  apply extend_later'; apply extend_sepcon_TT.
  intros jm jm' Delta' ge vx tx rho k F f TS [[[[TC3 TC1]  TC4] MT1] MT2] TC' Hcl Hge ? ? HGG.
  specialize (TC3 (m_phi jm') (age_laterR (age_jm_phi H))).
  specialize (TC1 (m_phi jm') (age_laterR (age_jm_phi H))).
  specialize (TC4 (m_phi jm') (age_laterR (age_jm_phi H))).
  specialize (MT1 (m_phi jm') (age_laterR (age_jm_phi H))).
  specialize (MT2 (m_phi jm') (age_laterR (age_jm_phi H))).
  apply (typecheck_tid_ptr_compare_sub _ _ TS) in TC2.
  pose proof TC1 as TC1'.
  pose proof TC3 as TC3'.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC' as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  apply (tc_expr_sub _ _ _ TS) in TC3'; [| auto].
  apply (tc_expr_sub _ _ _ TS) in TC1'; [| auto].
  exists jm', (PTree.set id (eval_expr (Ebinop cmp e1 e2 ty) rho) (tx)).
  econstructor.
  split; [reflexivity |].
  split3; auto.
  + apply age_level; auto.
  + normalize in H0.
    clear H H0.
    simpl. rewrite <- map_ptree_rel.
    apply guard_environ_put_te'; auto. subst. simpl.
    unfold construct_rho in *; auto.

    intros.

    destruct TC' as [TC' TC''].
    simpl in TC2. unfold typecheck_tid_ptr_compare in *.
    rewrite H in TC2.
    unfold guard_environ in *.

    destruct MT1 as [? [? [J1 [MT1 _]]]].
    destruct MT2 as [? [? [J2 [MT2 _]]]].
    destruct (mapsto_is_pointer _ _ _ _ MT1) as [? [? ?]].
    destruct (mapsto_is_pointer _ _ _ _ MT2) as [? [? ?]].

    destruct t; inv TC2.
    simpl. super_unfold_lift.
    simpl.
    apply tc_val_tc_val'.
    eapply pointer_cmp_no_mem_bool_type; eauto.
  + destruct H0.
    split; auto.
    - simpl.
      split3; auto.
      2: apply age1_resource_decay; auto.
      2:{
        split; [apply age_level; auto|].
        apply age1_ghost_of, age_jm_phi; auto.
      }
      destruct (age1_juicy_mem_unpack _ _ H).
      rewrite <- H3.
      econstructor; eauto.

      (*start new proof*)
      rewrite Hge in *.
      destruct TC'; simpl in H4, TC3, TC1.
      rewrite <- Hge in *.
      eapply Clight.eval_Ebinop.
      rewrite H3; eapply eval_expr_relate; eauto.
      rewrite H3; eapply eval_expr_relate; eauto.
      rewrite H3.
      super_unfold_lift.
      destruct MT1 as [? [? [J1 [MT1 _]]]].
      destruct MT2 as [? [? [J2 [MT2 _]]]].
      destruct (mapsto_is_pointer _ _ _ _ MT1) as [? [? ?]].
      destruct (mapsto_is_pointer _ _ _ _ MT2) as [? [? ?]].
      rewrite H6. rewrite H7. unfold eval_binop.
      rewrite <- H6. rewrite <- H7. clear H6 H7.
      (* rewrite HGG.*)
      apply (pointer_cmp_eval Delta' cmp e1 e2 sh1 sh2); auto;
      try (eauto; simpl; eauto).
    - split.
      2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.
      assert (app_pred (|>  (F rho * P rho)) (m_phi jm)).
      {
        rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto.
      }
      assert (laterR (m_phi jm) (m_phi jm')).
      {
        constructor 1.
        destruct (age1_juicy_mem_unpack _ _ H); auto.
      }
      specialize (H2 _ H3).
      eapply sepcon_derives; try  apply H2; auto.
      * clear - Hcl Hge.
        rewrite <- map_ptree_rel.
        specialize (Hcl rho (Map.set id (eval_expr (Ebinop cmp e1 e2 ty) rho) (make_tenv tx))).
        rewrite <- Hcl; auto.
        intros.
        destruct (Pos.eq_dec id i).
        {
          subst.
          left. unfold modifiedvars, modifiedvars', insert_idset.
          unfold insert_idset; rewrite PTree.gss; hnf; auto.
        }
        {
          right.
          rewrite Map.gso; auto. subst; auto.
        }
      * apply exp_right with (eval_id id rho).
        rewrite <- map_ptree_rel.
        assert (env_set
                 (mkEnviron (ge_of rho) (ve_of rho)
                    (Map.set id (eval_expr (Ebinop cmp e1 e2 ty) rho) (make_tenv tx))) id (eval_id id rho) = rho).
        {
          unfold env_set;
          f_equal.
          unfold eval_id; simpl.
          rewrite Map.override.
          rewrite Map.override_same. subst; auto.
          rewrite Hge in TC'.
          destruct TC' as [TC' _].
          destruct TC' as [TC' _]. unfold typecheck_temp_environ in *.
          simpl in TC2. unfold typecheck_tid_ptr_compare in *. remember ((temp_types Delta') ! id).
          destruct o; [ | inv TC2]. symmetry in Heqo.
          specialize (TC' _ _ Heqo). destruct TC'. destruct H4.
          simpl in H4.
          rewrite H4. simpl.
          f_equal. rewrite Hge; simpl. rewrite H4. reflexivity.
        }
        apply andp_right.
        {
          intros ? _. simpl.
          unfold subst.
          simpl in H4. super_unfold_lift.
          rewrite H4.
          unfold eval_id at 1. unfold force_val; simpl.
          rewrite Map.gss. auto.
        }
        {
          simpl. simpl in H4. super_unfold_lift.
          unfold subst.
          rewrite H4.
          auto.
        }
Qed.

Lemma semax_set_forward:
forall (Delta: tycontext) (P: assert) id e,
    semax Espec Delta
        (fun rho =>
          |> (tc_expr Delta e rho  && (tc_temp_id id (typeof e) Delta e rho) && P rho))
          (Sset id e)
        (normal_ret_assert
          (fun rho => (EX old:val,
                 !! (eval_id id rho =  subst id (`old) (eval_expr e) rho) &&
                            subst id (`old) P rho))).
Proof.
  intros until e.
  replace (fun rho : environ =>
     |>(tc_expr Delta e rho && tc_temp_id id (typeof e) Delta e rho &&
        P rho))
   with (fun rho : environ =>
       (|> tc_expr Delta e rho &&
        |> tc_temp_id id (typeof e) Delta e rho &&
        |> P rho))
    by (extensionality rho;  repeat rewrite later_andp; auto).
  apply semax_straight_simple; auto.
  intros jm jm' Delta' ge vx tx rho k F f TS [TC3 TC2] TC' Hcl Hge ? ? HGG'.
  specialize (TC3 (m_phi jm') (age_laterR (age_jm_phi H))).
  specialize (TC2 (m_phi jm') (age_laterR (age_jm_phi H))).
  assert (typecheck_environ Delta rho) as TC.
  {
    destruct TC' as [? _].
    eapply typecheck_environ_sub; eauto.
  }
  pose proof TC3 as TC3'.
  pose proof TC2 as TC2'.
  apply (tc_expr_sub _ _ _ TS) in TC3'; [| auto].
  apply (tc_temp_id_sub _ _ _ TS) in TC2'.
  exists jm', (PTree.set id (eval_expr e rho) (tx)).
  econstructor.
  split; [reflexivity |].
  split3; auto.
  + apply age_level; auto.
  + normalize in H0.
    clear - TS TC TC' TC2 TC2' TC3 TC3' Hge.
    simpl in *. simpl. rewrite <- map_ptree_rel.
    apply guard_environ_put_te'; auto.
    {
      subst; simpl in *.
      unfold construct_rho in *; auto.
    }
    intros. simpl in *. unfold typecheck_temp_id in *.
    unfold tc_temp_id in TC2'. simpl in TC2'. unfold typecheck_temp_id in TC2'.
    rewrite H in TC2'.
    simpl in *.
    rewrite denote_tc_assert_andp in TC2' ; simpl in *.
    super_unfold_lift. destruct TC2'.
    unfold tc_bool in *. remember (is_neutral_cast (implicit_deref (typeof e)) t).
    destruct b; inv H0.
    apply tc_val_tc_val'.
    apply @neutral_cast_tc_val with (Delta := Delta') (phi:=m_phi jm'); auto.
    unfold guard_environ in *. destruct TC'; auto.
  + destruct H0.
    split; auto.
    {
      simpl.
      split3; auto.
      + destruct (age1_juicy_mem_unpack _ _ H).
        rewrite <- H3.
        econstructor; eauto.
        rewrite H3; eapply eval_expr_relate with (m := jm'); eauto.
      + apply age1_resource_decay; auto.
      + split; [apply age_level; auto|].
        apply age1_ghost_of, age_jm_phi; auto.
    }
    split.
    2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.
    assert (app_pred (|>  (F rho * P rho)) (m_phi jm)).
    { rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto. }
    assert (laterR (m_phi jm) (m_phi jm')).
    { constructor 1. destruct (age1_juicy_mem_unpack _ _ H); auto. }
    specialize (H2 _ H3).
    eapply sepcon_derives; try  apply H2; auto.
    - clear - Hcl Hge.
      rewrite <- map_ptree_rel.
      specialize (Hcl rho (Map.set id (eval_expr e rho) (make_tenv tx))).
      rewrite <- Hcl; auto.
      intros.
      destruct (Pos.eq_dec id i).
      * subst.
        left. unfold modifiedvars, modifiedvars', insert_idset.
        unfold insert_idset; rewrite PTree.gss; hnf; auto.
      * right.
        rewrite Map.gso; auto. subst; auto.
    - apply exp_right with (eval_id id rho).
      rewrite <- map_ptree_rel.
      assert (env_set
               (mkEnviron (ge_of rho) (ve_of rho)
                  (Map.set id (eval_expr e rho) (make_tenv tx))) id (eval_id id rho) = rho).
      {
        unfold env_set;
        f_equal.
        unfold eval_id; simpl.
        rewrite Map.override.
        rewrite Map.override_same. subst; auto.
        rewrite Hge in TC'.
        destruct TC' as [TC' _].
        destruct TC' as [TC' _]. unfold typecheck_temp_environ in *.
        simpl in TC2'. unfold typecheck_temp_id in *. remember ((temp_types Delta') ! id).
        unfold tc_temp_id,typecheck_temp_id in TC2'. simpl in TC2'.
        rewrite <- Heqo in TC2'.
        destruct o; [ | inv TC2']. symmetry in Heqo.
        specialize (TC' _ _ Heqo). destruct TC'. destruct H4.
        simpl in H4.
        rewrite H4.
        f_equal. rewrite Hge; simpl. rewrite H4. reflexivity.
      }
      apply andp_right.
      * intros ? _. unfold liftx, lift; simpl.
        unfold subst.
        rewrite H4.
        unfold eval_id at 1. unfold force_val; simpl.
        rewrite Map.gss. auto.
      * unfold liftx, lift; simpl. unfold subst; rewrite H4.
        auto.
Qed.

Lemma semax_set_forward':
forall (Delta: tycontext) (P: assert) id e t,
    typeof_temp Delta id = Some t ->
    is_neutral_cast (typeof e) t = true ->
    semax Espec Delta
        (fun rho =>
          |> ((tc_expr Delta e rho) && P rho))
          (Sset id e)
        (normal_ret_assert
          (fun rho => (EX old:val,
                 !! (eval_id id rho =  subst id (`old) (eval_expr e) rho) &&
                            subst id (`old) P rho))).
Proof.
intros until e.
intros t H99 H98.
replace (fun rho : environ =>
   |> ((tc_expr Delta e rho) && P rho))
 with (fun rho : environ =>
     (|> tc_expr Delta e rho && |> P rho))
  by (extensionality rho;  repeat rewrite later_andp; auto).
apply semax_straight_simple; auto.
intros jm jm' Delta' ge vx tx rho k F f TS TC3 TC' Hcl Hge ? ? HGG'.
specialize (TC3 (m_phi jm') (age_laterR (age_jm_phi H))).
assert (typecheck_environ Delta rho) as TC.
{
  destruct TC'.
  eapply typecheck_environ_sub; eauto.
}
pose proof TC3 as TC3'.
apply (tc_expr_sub _ _ _ TS) in TC3'; [| auto].
assert (typeof_temp Delta' id = Some t) as H97.
  unfold typeof_temp in *.
  unfold tycontext_sub in TS. destruct TS as [?TS _]. specialize (TS id).
  destruct ((temp_types Delta) ! id); inversion H99.
  destruct ((temp_types Delta') ! id); inversion TS.
  subst; auto.
clear H99.
exists jm', (PTree.set id (eval_expr e rho) (tx)).
econstructor.
split.
reflexivity.
split3; auto.
+ apply age_level; auto.
+ normalize in H0.
  clear - TS TC TC' H98 H97 TC3 TC3' HGG' Hge.
  simpl in *. simpl. rewrite <- map_ptree_rel.
  apply guard_environ_put_te'; auto. subst; simpl in *.
  unfold construct_rho in *; auto.
  intros. simpl in *. unfold typecheck_temp_id in *.
  unfold typeof_temp in H97.
  rewrite H in H97.
  simpl in *.
  super_unfold_lift. inversion H97.
  subst.
  assert (is_neutral_cast (implicit_deref (typeof e)) t = true).
  destruct (typeof e), t; inversion H98; reflexivity.
  apply tc_val_tc_val'.
  apply @neutral_cast_tc_val with (Delta := Delta') (phi:=m_phi jm'); auto.
  apply neutral_isCastResultType; auto.
  unfold guard_environ in *. destruct TC'; auto.
+
  destruct H0.
  split; auto.
  simpl.
  split3; auto.
  destruct (age1_juicy_mem_unpack _ _ H).
  rewrite <- H3.
  econstructor; eauto.
  rewrite H3; eapply eval_expr_relate; try apply TC3; auto.
  apply age1_resource_decay; auto.
  split; [apply age_level; auto|].
  apply age1_ghost_of, age_jm_phi; auto.

split.
2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.

assert (app_pred (|>  (F rho * P rho)) (m_phi jm)).
rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto.
assert (laterR (m_phi jm) (m_phi jm')).
constructor 1.
destruct (age1_juicy_mem_unpack _ _ H); auto.
specialize (H2 _ H3).
eapply sepcon_derives; try  apply H2; auto.
clear - Hcl Hge.
rewrite <- map_ptree_rel.
specialize (Hcl rho (Map.set id (eval_expr e rho) (make_tenv tx))).
rewrite <- Hcl; auto.
intros.
destruct (Pos.eq_dec id i).
subst.
left. unfold modifiedvars, modifiedvars', insert_idset.
  rewrite PTree.gss; hnf; auto.
right.
rewrite Map.gso; auto. subst; auto.
apply exp_right with (eval_id id rho).
rewrite <- map_ptree_rel.
assert (env_set
         (mkEnviron (ge_of rho) (ve_of rho)
            (Map.set id (eval_expr e rho) (make_tenv tx))) id (eval_id id rho) = rho).
{ unfold env_set;
  f_equal.
  unfold eval_id; simpl.
  rewrite Map.override.
  rewrite Map.override_same. subst; auto.
  rewrite Hge in TC'.
  destruct TC' as [TC' _].
  destruct TC' as [TC' _]. unfold typecheck_temp_environ in *.
  unfold typeof_temp in H97. unfold typecheck_temp_id in *. remember ((temp_types Delta') ! id).
  destruct o; [ | inv H97]. symmetry in Heqo.
  specialize (TC' _ _ Heqo). destruct TC'. destruct H4.
  simpl in H4.
  rewrite H4. simpl.
  f_equal. rewrite Hge; simpl. rewrite H4. reflexivity.
}
unfold liftx, lift; simpl.
apply andp_right.
intros ? _. simpl.
unfold subst.
rewrite H4.
unfold eval_id at 1. unfold force_val; simpl.
rewrite Map.gss. auto.
unfold subst; rewrite H4.
auto.
Qed.

Lemma semax_cast_set:
forall (Delta: tycontext) (P: assert) id e t,
    typeof_temp Delta id = Some t ->
    semax Espec Delta
        (fun rho =>
          |> ((tc_expr Delta (Ecast e t) rho) && P rho))
          (Sset id (Ecast e t))
        (normal_ret_assert
          (fun rho => (EX old:val,
                 !! (eval_id id rho = subst id (`old) (eval_expr (Ecast e t)) rho) &&
                            subst id (`old) P rho))).
Proof.
intros until e.
intros t H99.
replace (fun rho : environ =>
   |> ((tc_expr Delta (Ecast e t) rho) && P rho))
 with (fun rho : environ =>
     (|> tc_expr Delta (Ecast e t) rho && |> P rho))
  by (extensionality rho;  repeat rewrite later_andp; auto).
apply semax_straight_simple; auto.
intros jm jm' Delta' ge vx tx rho k F f TS TC3 TC' Hcl Hge ? ? HGG'.
specialize (TC3 (m_phi jm') (age_laterR (age_jm_phi H))).
assert (typecheck_environ Delta rho) as TC.
{
  destruct TC'.
  eapply typecheck_environ_sub; eauto.
}
pose proof TC3 as TC3'.
apply (tc_expr_sub _ _ _ TS) in TC3'; [| auto].
assert (typeof_temp Delta' id = Some t) as H97.
  unfold typeof_temp in *.
  unfold tycontext_sub in TS. destruct TS as [?TS _]. specialize (TS id).
  destruct ((temp_types Delta) ! id); inversion H99.
  destruct ((temp_types Delta') ! id); inversion TS.
  subst; auto.
clear H99.
exists jm', (PTree.set id (eval_expr (Ecast e t) rho) (tx)).
econstructor.
split.
reflexivity.
split3; auto.
+ apply age_level; auto.
+ normalize in H0.
  clear - TS TC' TC H97 TC3 TC3' Hge HGG'.
  simpl in *. simpl. rewrite <- map_ptree_rel.
  apply guard_environ_put_te'; auto. subst; simpl in *.
  unfold construct_rho in *; auto.
  intros. simpl in *. unfold typecheck_temp_id in *.
  unfold typeof_temp in H97.
  rewrite H in H97.
  simpl in *.
  super_unfold_lift. inversion H97.
  subst.
  unfold tc_expr in TC3, TC3'; simpl in TC3, TC3'.
  rewrite denote_tc_assert_andp in TC3. destruct TC3.
  rewrite denote_tc_assert_andp in TC3'. destruct TC3'.
  apply tc_val_tc_val'.
  apply @tc_val_sem_cast with (Delta := Delta') (phi:=m_phi jm'); auto.
  eapply guard_environ_e1; eauto.
+
  destruct H0.
  split; auto.
  simpl.
  split3; auto.
  destruct (age1_juicy_mem_unpack _ _ H).
  rewrite <- H3.
  econstructor; eauto.
  change ((`(force_val1 (sem_cast (typeof e) t)) (eval_expr e) rho)) with (eval_expr (Ecast e t) rho).
  rewrite H3; eapply eval_expr_relate; eauto.
  apply age1_resource_decay; auto.
  split; [apply age_level; auto|].
  apply age1_ghost_of, age_jm_phi; auto.

split.
2: eapply pred_hereditary; try apply H1; destruct (age1_juicy_mem_unpack _ _ H); auto.

assert (app_pred (|>  (F rho * P rho)) (m_phi jm)).
rewrite later_sepcon. eapply sepcon_derives; try apply H0; auto.
assert (laterR (m_phi jm) (m_phi jm')).
constructor 1.
destruct (age1_juicy_mem_unpack _ _ H); auto.
specialize (H2 _ H3).
eapply sepcon_derives; try  apply H2; auto.
clear - Hcl Hge.
rewrite <- map_ptree_rel.
specialize (Hcl rho (Map.set id (eval_expr (Ecast e t) rho) (make_tenv tx))).
rewrite <- Hcl; auto.
intros.
destruct (Pos.eq_dec id i).
subst.
left. unfold modifiedvars, modifiedvars', insert_idset.
 rewrite PTree.gss; hnf; auto.
right.
rewrite Map.gso; auto. subst; auto.
apply exp_right with (eval_id id rho).
rewrite <- map_ptree_rel.
assert (env_set
         (mkEnviron (ge_of rho) (ve_of rho)
            (Map.set id (eval_expr (Ecast e t) rho) (make_tenv tx))) id (eval_id id rho) = rho).
{ unfold env_set;
  f_equal.
  unfold eval_id; simpl.
  rewrite Map.override.
  rewrite Map.override_same. subst; auto.
  rewrite Hge in TC'.
  destruct TC' as [TC' _].
  destruct TC' as [TC' _]. unfold typecheck_temp_environ in *.
  unfold typeof_temp in H97. unfold typecheck_temp_id in *. remember ((temp_types Delta') ! id).
  destruct o; [ | inv H97]. symmetry in Heqo.
  specialize (TC' _ _ Heqo). destruct TC'. destruct H4.
  simpl in H4.
  rewrite H4. simpl.
  f_equal. rewrite Hge; simpl. rewrite H4. reflexivity.
}

apply andp_right.
- unfold liftx, lift; simpl. intros ? _. simpl. unfold subst.
  change ((`(force_val1 (sem_cast (typeof e) t)) (eval_expr e) rho)) with (eval_expr (Ecast e t) rho).
  rewrite H4.
  unfold eval_id at 1. unfold force_val; simpl.
  rewrite Map.gss. auto.
- unfold liftx, lift; simpl. (*rewrite <- H4. simpl.*)
  unfold subst. simpl.
  change ((`(force_val1 (sem_cast (typeof e) t)) (eval_expr e) rho)) with (eval_expr (Ecast e t) rho).
  rewrite H4; trivial.
Qed.

Lemma eval_cast_Vundef:
 forall t1 t2, eval_cast t1 t2 Vundef = Vundef.
Proof.
 intros.
 unfold eval_cast, sem_cast, classify_cast.
 destruct (eqb_type t1 int_or_ptr_type);
 destruct (eqb_type t2 int_or_ptr_type);
 destruct t1,t2;
 try destruct i; try destruct s; try destruct f;
 try destruct i0; try destruct s0; try destruct f0;
 reflexivity.
Qed.

Transparent Int.repr.

Lemma eqb_attr_true:
  forall a a',  eqb_attr a a' = true  -> a=a'.
Proof.
intros.
destruct a as [v a],a' as [v' a'].
simpl in H.
apply andb_true_iff in H.
destruct H.
destruct v,v'; inv  H;
destruct a,a'; inv H0; auto;
apply Neqb_ok in H1; subst n0; auto.
Qed.

Opaque Int.repr.

Lemma semax_load:
forall (Delta: tycontext) sh id P e1 t2 v2,
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
   (forall rho, seplog.derives (!! typecheck_environ Delta rho && P rho) (mapsto sh (typeof e1) (eval_lvalue e1 rho) v2 * TT)) ->
    semax Espec Delta
       (fun rho => |>
        (tc_lvalue Delta e1 rho
        && (!! tc_val (typeof e1) v2) && P rho))
       (Sset id e1)
       (normal_ret_assert (fun rho =>
        EX old:val, (!!(eval_id id rho = v2) &&
                         (subst id (`old) P rho)))).
Proof.
intros until v2.
intros Hid TC1 H_READABLE H99.
replace (fun rho : environ => |> ((tc_lvalue Delta e1 rho &&
  !! tc_val (typeof e1) v2 && P rho)))
 with (fun rho : environ =>
   ( |> tc_lvalue Delta e1 rho &&
     |> !! (tc_val (typeof e1) v2) &&
     |> P rho)).
2 : { extensionality rho. repeat rewrite <- later_andp. f_equal. }
repeat rewrite andp_assoc.
unfold mapsto.
apply semax_straight_simple.
intro. apply boxy_andp; auto.
intros jm jm1 Delta' ge ve te rho k F f TS [TC2 TC3] TC' Hcl Hge ? ? HGG'.
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi H))).
specialize (TC3 (m_phi jm1) (age_laterR (age_jm_phi H))).
assert (typecheck_environ Delta rho) as TC.
{ destruct TC'. eapply typecheck_environ_sub; eauto. }
pose proof TC2 as TC2'.
apply (tc_lvalue_sub _ _ _ TS) in TC2'; [| auto].
hnf in TC3.
apply (typeof_temp_sub _ _ TS) in Hid.
assert (H99': forall rho : environ,
      !!typecheck_environ Delta' rho && P rho
      |-- mapsto sh (typeof e1) (eval_lvalue e1 rho) v2 * TT).
intro; eapply derives_trans; [ | apply H99]; apply andp_derives; auto.
intros ? ?; do 3 red.
eapply typecheck_environ_sub; eauto.
clear H99.
destruct (eval_lvalue_relate _ _ _ _ _ e1 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC')) as [b [ofs [? ?]]]; auto.
rewrite <- (age_jm_dry H) in H1.
exists jm1.
exists (PTree.set id v2 te).
econstructor; split; [reflexivity | ].
split3.
apply age_level; auto. simpl.
rewrite <- map_ptree_rel.
apply guard_environ_put_te'.
unfold typecheck_temp_id in *.
unfold construct_rho in *. destruct rho; inv Hge; auto.
clear - H_READABLE Hid TC1 TC2 TC3 TC' H2 Hge H0 H99'.
intros. simpl in TC1.
unfold typeof_temp in Hid. rewrite H in Hid.
inv Hid.
apply tc_val_tc_val'.
apply (neutral_cast_subsumption _ t2 _ TC1 TC3).
(* typechecking proof *)
split; [split3 | ].
* simpl.
   rewrite <- (age_jm_dry H); constructor; auto.
   apply Clight.eval_Elvalue with b ofs Full; auto.
   destruct H0 as [H0 _].
   assert ((|> (F rho * P rho))%pred
       (m_phi jm)).
   rewrite later_sepcon.
   eapply sepcon_derives; try apply H0; auto.
   specialize (H3 _ (age_laterR (age_jm_phi H))).
   rewrite sepcon_comm in H3.
   assert ((mapsto sh (typeof e1) (eval_lvalue e1 rho) v2 * TT)%pred (m_phi jm1)).
   rewrite <- TT_sepcon_TT. rewrite <- sepcon_assoc.
   eapply sepcon_derives; try apply H3; auto.
   eapply derives_trans; [ | apply H99'].
   apply andp_right; auto. intros ? _ ; do 3 red. destruct TC'; auto.
   clear H3; rename H4 into H3.
   destruct H3 as [m1 [m2 [? [? _]]]].
   unfold mapsto in H4.
   revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
   rename m into ch.
   rewrite H2 in H5.
   destruct (type_is_volatile (typeof e1)); try contradiction.
   rewrite if_true in H5 by auto.
   destruct H5 as [[H5' H5] | [H5 _]]; [ | rewrite H5 in TC3; exfalso; revert TC3; apply tc_val_Vundef].
   assert (core_load ch  (b, Ptrofs.unsigned ofs) v2 (m_phi jm1)).
   apply mapsto_core_load with sh.
   exists m1; exists m2; split3; auto.
   apply Clight.deref_loc_value with ch; auto.
   unfold loadv.
   rewrite (age_jm_dry H).
   apply core_load_load.
   intros.
   destruct H6 as [bl [_ ?]]. specialize (H6 (b,z)). hnf in H6.
   rewrite if_true in H6 by (split; auto; lia).
   destruct H6 as [? [? ?]]. rewrite H6. simpl.
   clear - x0.
   unfold perm_of_sh. if_tac. if_tac; constructor. if_tac; [ | contradiction]. constructor.
   apply H6.
* apply age1_resource_decay; auto.
* split; [apply age_level; auto|].
  apply age1_ghost_of, age_jm_phi; auto.
* rewrite <- map_ptree_rel.
  rewrite <- (Hcl rho (Map.set id v2 (make_tenv te))).
 +normalize.
   exists (eval_id id rho).
   destruct H0.
   apply later_sepcon2 in H0.
   specialize (H0 _ (age_laterR (age_jm_phi H))).
   split; [ |  apply pred_hereditary with (m_phi jm); auto; apply age_jm_phi; eauto].
   eapply sepcon_derives; try apply H0; auto.
   assert (env_set
         (mkEnviron (ge_of rho) (ve_of rho) (Map.set id v2 (make_tenv te))) id
         (eval_id id rho) = rho).
  unfold env_set. simpl.
  rewrite Map.override. unfold eval_id.
  destruct TC' as [TC' _].
  unfold typecheck_environ in TC'. repeat rewrite andb_true_iff in TC'. destruct TC' as [TC'[ _ _]].
  unfold typecheck_temp_environ in *.
  specialize (TC' id).
  unfold typeof_temp in Hid. destruct ((temp_types Delta') ! id); inv Hid.
  specialize (TC' _ (eq_refl _)).
   destruct TC'. destruct H4. rewrite H4. simpl.
  rewrite Map.override_same; subst; auto.
  unfold liftx, lift; simpl. unfold subst.
  rewrite H4.
  apply andp_right; auto.
  intros ? ?; simpl.
  unfold eval_id, force_val. simpl. rewrite Map.gss. auto.
 +intro i; destruct (Pos.eq_dec id i); [left; auto | right; rewrite Map.gso; auto].
   subst; unfold modifiedvars, modifiedvars', insert_idset.
   rewrite PTree.gss; hnf; auto.
   subst. auto.
Qed.


Lemma semax_cast_load:
forall (Delta: tycontext) sh id P e1 t1 v2,
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
   (forall rho, seplog.derives (!! typecheck_environ Delta rho && P rho) (mapsto sh (typeof e1) (eval_lvalue e1 rho) v2 * TT)) ->
    semax Espec Delta
       (fun rho => |>
        (tc_lvalue Delta e1 rho
        && (!! tc_val t1 (`(eval_cast (typeof e1) t1 v2) rho))
        &&  P rho))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (fun rho =>
        EX old:val, (!!(eval_id id rho = (`(eval_cast (typeof e1) t1 v2)) rho) &&
                         (subst id (`old) P rho)))).
Proof.
intros until v2.
intros Hid HCAST H_READABLE H99.
replace (fun rho : environ => |> ((tc_lvalue Delta e1 rho &&
       (!! tc_val t1  (`(eval_cast (typeof e1) t1 v2) rho)) &&
       P rho)))
 with (fun rho : environ =>
   ( |> tc_lvalue Delta e1 rho &&
     |> !! (tc_val t1 (eval_cast (typeof e1) t1 v2)) &&
     |> P rho)).
2 : { extensionality rho. repeat rewrite <- later_andp. f_equal. }
repeat rewrite andp_assoc.
unfold mapsto.
apply semax_straight_simple.
intro. apply boxy_andp; auto.
intros jm jm1 Delta' ge ve te rho k F f TS [TC2 TC3] TC' Hcl Hge ? ? HGG'.
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi H))).
specialize (TC3 (m_phi jm1) (age_laterR (age_jm_phi H))).
assert (typecheck_environ Delta rho) as TC.
{ destruct TC'. eapply typecheck_environ_sub; eauto. }
pose proof TC2 as TC2'.
apply (tc_lvalue_sub _ _ _ TS) in TC2'; [| auto].
hnf in TC3.
apply (typeof_temp_sub _ _ TS) in Hid.
assert (H99': forall rho : environ,
      !!typecheck_environ Delta' rho && P rho
      |-- mapsto sh (typeof e1) (eval_lvalue e1 rho) v2 * TT).
{ intros.
  intro; eapply derives_trans; [ | apply H99]; apply andp_derives; auto.
  intros ? ?; do 3 red.
  eapply typecheck_environ_sub; eauto.
}
clear H99.
destruct (eval_lvalue_relate _ _ _ _ _ e1 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC')) as [b [ofs [? ?]]]; auto.
rewrite <- (age_jm_dry H) in H1.
exists jm1.
exists (PTree.set id (eval_cast (typeof e1) t1 v2) (te)).
econstructor.
split.
reflexivity.
split3.
apply age_level; auto. simpl.
rewrite <- map_ptree_rel.
apply guard_environ_put_te'.
unfold typecheck_temp_id in *.
unfold construct_rho in *. destruct rho; inv Hge; auto.
clear - H_READABLE Hid TC2 TC3 TC' H2 Hge H0 H99'.
intros.
unfold typeof_temp in Hid. rewrite H in Hid.
inv Hid.
simpl.
apply tc_val_tc_val'.
apply TC3.
split; [split3 | ].
*   rewrite <- (age_jm_dry H); constructor; auto.
  destruct (sem_cast (typeof e1) t1 v2) eqn:EC.
  2: elimtype False; clear - EC TC3;
    unfold eval_cast, force_val1 in TC3; rewrite EC in TC3;
    destruct t1; try destruct f;
    try destruct (eqb_type _ _); contradiction.
  destruct H0 as [H0 _].
   assert ((|> (F rho * P rho))%pred (m_phi jm)). {
    rewrite later_sepcon.
    eapply sepcon_derives; try apply H0; auto.
  }
  specialize (H3 _ (age_laterR (age_jm_phi H))).
  rewrite sepcon_comm in H3.
  assert ((mapsto sh (typeof e1) (eval_lvalue e1 rho) v2 * TT)%pred (m_phi jm1)). {
    rewrite <- TT_sepcon_TT. rewrite <- sepcon_assoc.
    eapply sepcon_derives; try apply H3; auto.
    eapply derives_trans; [ | apply H99'].
    apply andp_right; auto. intros ? _ ; do 3 red. destruct TC'; auto.
 }
   clear H3; rename H4 into H3.
   destruct H3 as [m1 [m2 [? [? _]]]].
   unfold mapsto in H4.
   revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
   rename m into ch.
   destruct (type_is_volatile (typeof e1)) eqn:NONVOL; try contradiction.
   rewrite H2 in H5.
   rewrite if_true in H5 by auto.
   destruct H5 as [[H5' H5] | [H5 _]];
    [ | hnf in TC3; rewrite H5, eval_cast_Vundef in TC3; exfalso; revert TC3; apply tc_val_Vundef].
   apply Clight.eval_Ecast with v2.
  2: apply sem_cast_e1; auto;
      unfold eval_cast, force_val1; rewrite !EC; reflexivity.
   eapply Clight.eval_Elvalue; eauto.
   assert (core_load ch  (b, Ptrofs.unsigned ofs) v2 (m_phi jm1)).
   apply mapsto_core_load with sh.
   exists m1; exists m2; split3; auto.
   apply Clight.deref_loc_value with ch; auto.
   unfold loadv.
   rewrite (age_jm_dry H).
   apply core_load_load.
   intros.
   destruct H6 as [bl [_ ?]]. specialize (H6 (b,z)). hnf in H6.
   rewrite if_true in H6 by (split; auto; lia).
   destruct H6 as [? [? ?]]. rewrite H6. simpl.
   clear - x0.
   unfold perm_of_sh. if_tac. if_tac; constructor. if_tac; [ | contradiction]. constructor.
   apply H6.
* apply age1_resource_decay; auto.
* split; [apply age_level; auto|].
  apply age1_ghost_of, age_jm_phi; auto.
* rewrite <- map_ptree_rel.
  rewrite <- (Hcl rho (Map.set id (eval_cast (typeof e1) t1 v2) (make_tenv te))).
 + normalize.
   exists (eval_id id rho).
   destruct H0.
   apply later_sepcon2 in H0.
   specialize (H0 _ (age_laterR (age_jm_phi H))).
   split; [ |  apply pred_hereditary with (m_phi jm); auto; apply age_jm_phi; eauto].
   eapply sepcon_derives; try apply H0; auto.
   assert (env_set
         (mkEnviron (ge_of rho) (ve_of rho) (Map.set id (eval_cast (typeof e1) t1 v2) (make_tenv te))) id
         (eval_id id rho) = rho).
  unfold env_set. simpl.
  rewrite Map.override. unfold eval_id.
  destruct TC' as [TC' _].
  unfold typecheck_environ in TC'. repeat rewrite andb_true_iff in TC'. destruct TC' as [TC'[ _ _]].
  unfold typecheck_temp_environ in *.
  specialize (TC' id).
  unfold typeof_temp in Hid. destruct ((temp_types Delta') ! id); inv Hid.
  specialize (TC' _ (eq_refl _)).
   destruct TC'. destruct H4. rewrite H4. simpl.
  rewrite Map.override_same; subst; auto.
  unfold subst. simpl.
 (* rewrite H4.*)
  apply andp_right; auto.
  - intros ? ?; simpl. unfold liftx, lift; simpl.
    unfold eval_id, force_val. simpl. rewrite Map.gss. auto.
  - unfold eval_cast, force_val1 in H4. unfold liftx, lift; simpl. rewrite H4; trivial.
 + intro i; destruct (Pos.eq_dec id i); [left; auto | right; rewrite Map.gso; auto].
   subst; unfold modifiedvars, modifiedvars', insert_idset.
   rewrite PTree.gss; hnf; auto.
   subst. auto.
Qed.

Lemma res_option_core: forall r, res_option (core r) = None.
Proof.
 destruct r. rewrite core_NO; auto. rewrite core_YES; auto. rewrite core_PURE; auto.
Qed.

Lemma writable0_lub_retainer_Rsh:
 forall sh, writable0_share sh ->
  Share.lub (retainer_part sh) Share.Rsh = sh.
  intros. symmetry.
  unfold retainer_part.
  rewrite (comp_parts comp_Lsh_Rsh sh) at 1.
  f_equal; auto.
  unfold writable0_share in H.
  apply leq_join_sub in H.  apply Share.ord_spec1 in H. auto.
Qed.

Definition decode_encode_val_ok (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | Mint8signed, Mint8signed => True
  | Mint8unsigned, Mint8signed => True
  | Mint8signed, Mint8unsigned => True
  | Mint8unsigned, Mint8unsigned => True
  | Mint16signed, Mint16signed => True
  | Mint16unsigned, Mint16signed => True
  | Mint16signed, Mint16unsigned => True
  | Mint16unsigned, Mint16unsigned => True
  | Mint32, Mfloat32 => True
  | Many32, Many32 => True
  | Many64, Many64 => True
  | Mint32, Mint32 => True
  | Mint64, Mint64 => True
  | Mint64, Mfloat64 => True
  | Mfloat64, Mfloat64 =>  True
  | Mfloat64, Mint64 =>  True
  | Mfloat32, Mfloat32 =>  True
  | Mfloat32, Mint32 =>  True
  | _,_ => False
  end.

Lemma decode_encode_val_ok_same:  forall ch,
    decode_encode_val_ok ch ch.
Proof.
destruct ch; simpl; auto.
Qed.

Lemma decode_encode_val_fun:
  forall ch1 ch2, decode_encode_val_ok ch1 ch2 ->
  forall v v1 v2,
     decode_encode_val v ch1 ch2 v1 ->
     decode_encode_val v ch1 ch2 v2 ->
     v1=v2.
Proof.
intros.
destruct ch1, ch2; try contradiction;
destruct v; simpl in *; subst; auto.
Qed.

Lemma decode_encode_val_ok1:
  forall v ch ch' v',
 decode_encode_val_ok ch ch' ->
 decode_encode_val v ch ch' v' ->
 decode_val ch' (encode_val ch v) = v'.
Proof.
intros.
destruct ch, ch'; try contradiction;
destruct v; auto;
simpl in H0; subst;
unfold decode_val, encode_val;
try rewrite proj_inj_bytes;
rewrite ?decode_encode_int_1, ?decode_encode_int_2,
  ?decode_encode_int_4,
  ?decode_encode_int_8;
f_equal;
rewrite ?Int.sign_ext_zero_ext by reflexivity;
rewrite ?Int.zero_ext_sign_ext by reflexivity;
rewrite ?Int.zero_ext_idem by (compute; congruence);
auto.
all: try solve [
simpl; destruct Archi.ptr64; simpl; auto;
rewrite proj_sumbool_is_true by auto;
rewrite proj_sumbool_is_true by auto;
simpl; auto].
apply Float32.of_to_bits.
apply Float.of_to_bits.
Qed.

Lemma decode_encode_val_size:
  forall ch1 ch2, decode_encode_val_ok ch1 ch2 ->
   size_chunk ch1 = size_chunk ch2.
Proof.
intros.
destruct ch1, ch2; try contradiction;
simpl in *; subst; auto.
Qed.

Theorem load_store_similar':
   forall (chunk : memory_chunk) (m1 : Memory.mem)
         (b : block) (ofs : Z) (v : val) (m2 : Memory.mem),
       store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  (align_chunk chunk' | ofs) ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk' b ofs).
  split; auto.
  destruct (store_valid_access_1 _ _ _ _ _ _ H _ _ _ _ (store_valid_access_3 _ _ _ _ _ _ H)).
  rewrite H0.
  eapply range_perm_implies; eauto. constructor.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B.
  rewrite (store_mem_contents _ _ _ _ _ _ H).
  rewrite PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H0.
  apply Nat2Z.inj; auto.
Qed.

Lemma address_mapsto_can_store': forall jm ch ch' v sh (wsh: writable0_share sh) b ofs v' my,
       (address_mapsto ch v sh (b, Ptrofs.unsigned ofs) * exactly my)%pred (m_phi jm) ->
       decode_encode_val_ok ch ch' ->
       (align_chunk ch' | Ptrofs.unsigned ofs) ->
       exists m',
       {H: Mem.store ch (m_dry jm) b (Ptrofs.unsigned ofs) v' = Some m'|
       ((EX v'':val, !! (decode_encode_val v' ch ch' v'') &&
          address_mapsto ch' v'' sh (b, Ptrofs.unsigned ofs)) * exactly my)%pred
       (m_phi (store_juicy_mem _ _ _ _ _ _ H))}.
Proof.
intros * wsh * H OK AL.
destruct (mapsto_can_store ch v sh wsh b (Ptrofs.unsigned ofs) jm v') as [m' STORE]; auto.
eapply sepcon_derives; eauto.
exists m'.
exists STORE.
pose proof I.
destruct H as [m1 [m2 [? [? Hmy]]]].
do 3 red in Hmy.
assert (H2 := I); assert (H3 := I).
forget (Ptrofs.unsigned ofs) as i. clear ofs.
pose (f loc := if adr_range_dec (b,i) (size_chunk ch) loc
                      then YES (Share.lub (res_retain (m1 @ loc)) Share.Rsh)
                               (readable_share_lub (writable0_readable writable0_Rsh))
                               (VAL (contents_at m' loc)) NoneP
                     else core (m_phi jm @ loc)).
destruct (make_rmap f (ghost_of m1) (level jm)) as [mf [? [? Hg]]]; auto.
{ unfold f, compose; clear f; extensionality loc.
  symmetry. if_tac.
  unfold resource_fmap. rewrite preds_fmap_NoneP.
  reflexivity.
  generalize (resource_at_approx (m_phi jm) loc);
  destruct (m_phi jm @ loc); [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; try reflexivity.
  auto. }
{ rewrite level_juice_level_phi. apply join_level in H as [<- _]. apply ghost_of_approx. }
unfold f in H5; clear f.
exists mf; exists m2; split3; auto.
apply resource_at_join2.
rewrite H4. symmetry. apply (level_store_juicy_mem _ _ _ _ _ _ STORE).
apply join_level in H; destruct H.
change R.rmap with rmap in *. change R.ag_rmap with ag_rmap in *.
rewrite H6; symmetry. apply (level_store_juicy_mem _ _ _ _ _ _ STORE).
intro; rewrite H5. clear mf H4 H5 Hg.
simpl m_phi.
apply (resource_at_join _ _ _ loc) in H.
destruct H1 as [vl [? ?]]. specialize (H4 loc). hnf in H4.
if_tac.
destruct H4. hnf in H4. rewrite H4 in H.
rewrite (proof_irr x (writable0_readable wsh)) in *; clear x.
destruct (YES_join_full _ _ _ _ _ _ H) as [sh' [nsh' H6]]; auto.
rewrite H6.
unfold inflate_store; simpl.
rewrite resource_at_make_rmap.
rewrite H6 in H.
inversion H; clear H.
subst sh2 k sh p.
constructor.
rewrite H4; simpl.
rewrite writable0_lub_retainer_Rsh; auto.
apply join_unit1_e in H; auto.
rewrite H.
unfold inflate_store.
rewrite resource_at_make_rmap.
rewrite resource_at_approx.
case_eq (m_phi jm @ loc); intros.
rewrite core_NO. constructor. apply join_unit1; auto.
destruct k; try solve [rewrite core_YES; constructor; apply join_unit1; auto].
rewrite core_YES.
destruct (juicy_mem_contents _ _ _ _ _ _ H6). subst p.
pose proof (store_phi_elsewhere_eq _ _ _ _ _ _ STORE _ _ _ _ H5 H6).
rewrite H8.
constructor.
apply join_unit1; auto.
rewrite core_PURE; constructor.
rewrite Hg; simpl.
unfold inflate_store; rewrite ghost_of_make_rmap.
apply ghost_of_join; auto.

unfold address_mapsto in *.
destruct (load_store_similar' _ _ _ _ _ _ STORE ch' (eq_sym (decode_encode_val_size _ _ OK)))
  as [v'' [LD DE]]; auto.
exists v''.
rewrite prop_true_andp by auto.
exists (encode_val ch v').
destruct H1 as [vl [[? [? ?]] ?]].
split.
split3; auto.
rewrite encode_val_length.
clear - OK. apply decode_encode_val_size in OK.
   rewrite !size_chunk_conv in OK. apply Nat2Z.inj; auto.
apply decode_encode_val_ok1; auto.

intro loc. hnf.
if_tac. exists (writable0_readable wsh).
hnf; rewrite H5.
rewrite if_true; auto.
assert (STORE' := Mem.store_mem_contents _ _ _ _ _ _ STORE).
pose proof (juicy_mem_contents (store_juicy_mem jm m' ch b i v' STORE)).
pose proof (juicy_mem_access (store_juicy_mem jm m' ch b i v' STORE)).
pose proof (juicy_mem_max_access (store_juicy_mem jm m' ch b i v' STORE)).
pose proof I.
unfold contents_cohere in H10.
rewrite preds_fmap_NoneP.
f_equal.
specialize (H8 loc). rewrite jam_true in H8 by (rewrite (decode_encode_val_size _ _ OK); auto).
destruct H8. hnf in H8. rewrite H8. simpl; auto.
f_equal.
clear - STORE H1 H9 OK AL DE.
destruct loc as [b' z].
destruct H9.
subst b'.
rewrite (nth_getN m' b _ _ _ H0).
rewrite (store_mem_contents _ _ _ _ _ _ STORE).
rewrite PMap.gss.
replace (Z.to_nat (size_chunk ch)) with (size_chunk_nat ch) by (destruct ch; simpl; auto).
rewrite <- (decode_encode_val_size _ _ OK).
fold (size_chunk_nat ch).
rewrite <- (encode_val_length ch v').
rewrite getN_setN_same.
apply YES_ext.
apply (writable0_lub_retainer_Rsh _ wsh).
generalize (size_chunk_pos ch'); lia.
rewrite (decode_encode_val_size _ _ OK); auto.
do 3 red. rewrite H5.
rewrite (decode_encode_val_size _ _ OK).
 rewrite if_false by auto.
apply core_identity.
Qed.


Lemma address_mapsto_can_store: forall jm ch v sh (wsh: writable0_share sh) b ofs v' my,
       (address_mapsto ch v sh (b, Ptrofs.unsigned ofs) * exactly my)%pred (m_phi jm) ->
       decode_val ch (encode_val ch v') = v' ->
       exists m',
       {H: Mem.store ch (m_dry jm) b (Ptrofs.unsigned ofs) v' = Some m'|
       (address_mapsto ch v' sh (b, Ptrofs.unsigned ofs) * exactly my)%pred
       (m_phi (store_juicy_mem _ _ _ _ _ _ H))}.
Proof.
intros.
pose proof (address_mapsto_can_store' _ _ ch _ _ wsh _ _ v' _ H (decode_encode_val_ok_same _)).
destruct H1 as [m' [? ?]].
destruct H as [? [? [_ [[? [[ _ [_ ?]] _]] _]]]]; auto.
rewrite exp_sepcon1 in a.
destruct a as [v'' ?].
rewrite sepcon_andp_prop1 in H1.
destruct H1.
do 3 red in H1.
pose proof (decode_encode_val_general v' ch ch).
rewrite H0 in H3.
pose proof (decode_encode_val_fun _ _  (decode_encode_val_ok_same ch) _ _ _  H1 H3).
subst v''.
exists m'.
exists x.
auto.
Qed.

Ltac dec_enc :=
match goal with
[ |- decode_val ?CH _ = ?V] => assert (DE := decode_encode_val_general V CH CH);
                               apply decode_encode_val_similar in DE; auto
end.

Lemma load_cast:
 forall (t: type) (e2 : expr) (ch : memory_chunk) rho phi m,
   tc_val (typeof e2) (eval_expr e2 rho) ->
   denote_tc_assert (isCastResultType (typeof e2) t e2)
     rho phi ->
   access_mode t = By_value ch ->
   Val.load_result ch
     (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) t m)) =
   force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) t m).
Proof.
intros.
assert (size_chunk ch = sizeof t). {
  clear - H1.
  destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ], ch; inv H1; reflexivity.
}
unfold sizeof in *.
destruct ch;
 destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; try solve [inv H1];
simpl in *;
 try solve [inv H1]; clear H1; destruct (eval_expr e2 rho);
 destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] ;
 try solve [inv H];
unfold Cop.sem_cast; simpl;
destruct Archi.ptr64 eqn:Hp;
try destruct (Float.to_int f);
try destruct (Float.to_intu f);
try destruct (Float.to_long f);
try destruct (Float.to_longu f);
try destruct (Float32.to_int f);
try destruct (Float32.to_intu f);
try destruct (Float32.to_long f);
try destruct (Float32.to_longu f);
 auto; simpl;
try solve [try rewrite Int.sign_ext_idem; auto; simpl; lia];
try rewrite Int.zero_ext_idem; auto; simpl; try lia;
try solve [simple_if_tac; auto].
Qed.


Lemma semax_store:
 forall Delta e1 e2 sh P,
   writable0_share sh ->
   semax Espec Delta
          (fun rho =>
          |> (tc_lvalue Delta e1 rho && tc_expr Delta (Ecast e2 (typeof e1)) rho  &&
             (mapsto_ sh (typeof e1) (eval_lvalue e1 rho) * P rho)))
          (Sassign e1 e2)
          (normal_ret_assert (fun rho => mapsto sh (typeof e1) (eval_lvalue e1 rho)
                                           (force_val (sem_cast  (typeof e2) (typeof e1) (eval_expr e2 rho))) * P rho)).
Proof.
intros until P. intros WS.
apply semax_pre with
  (fun rho : environ =>
   EX v3: val,
      |> tc_lvalue Delta e1 rho && |> tc_expr Delta (Ecast e2 (typeof e1)) rho &&
      |> (mapsto sh (typeof e1) (eval_lvalue e1 rho) v3 * P rho)).
intro. apply andp_left2.
unfold mapsto_.
apply exp_right with Vundef.
repeat rewrite later_andp; auto.
apply extract_exists_pre; intro v3.
apply semax_straight_simple; auto.
intros jm jm1 Delta' ge ve te rho k F f TS [TC1 TC2] TC4 Hcl Hge Hage [H0 H0'] HGG'.
specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
assert (typecheck_environ Delta rho) as TC.
{ destruct TC4. eapply typecheck_environ_sub; eauto. }
pose proof TC1 as TC1'.
pose proof TC2 as TC2'.
apply (tc_lvalue_sub _ _ _ TS) in TC1'; [| auto].
apply (tc_expr_sub _ _ _ TS) in TC2'; [| auto].
unfold tc_expr in TC2, TC2'; simpl in TC2, TC2'.
rewrite denote_tc_assert_andp in TC2, TC2'.
simpl in TC2,TC2'; super_unfold_lift.
destruct TC2 as [TC2 TC3].
destruct TC2' as [TC2' TC3'].
apply later_sepcon2 in H0.
specialize (H0 _ (age_laterR (age_jm_phi Hage))).
pose proof I.
destruct H0 as [?w [?w [? [? [?w [?w [H3 [H4 H5]]]]]]]].
unfold mapsto in H4.
revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
rename H2 into Hmode. rename m into ch.
destruct (eval_lvalue_relate _ _ _ _ _ e1 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC4)) as [b0 [i [He1 He1']]]; auto.
rewrite He1' in *.
destruct (join_assoc H3 (join_comm H0)) as [?w [H6 H7]].
destruct (type_is_volatile (typeof e1)) eqn:NONVOL; try contradiction.
rewrite if_true in H4 by auto.
assert (exists v, address_mapsto ch v
             sh
        (b0, Ptrofs.unsigned i) w1)
       by (destruct H4 as [[H4' H4] |[? [? ?]]]; eauto).
clear v3 H4; destruct H2 as [v3 H4].

assert (H11': (res_predicates.address_mapsto ch v3 sh
        (b0, Ptrofs.unsigned i) * TT)%pred (m_phi jm1))
 by (exists w1; exists w3; split3; auto).
assert (H11: (res_predicates.address_mapsto ch v3  sh
        (b0, Ptrofs.unsigned i) * exactly w3)%pred (m_phi jm1)).
{ exists w1; exists w3; split3; auto.
  hnf; eauto. }
apply address_mapsto_can_store
   with (v':=((force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))))) in H11;
  auto.
2: {
  unfold typecheck_store in *.
  destruct TC4 as [TC4 _].
  simpl in TC2'. apply typecheck_expr_sound in TC2'; auto.
  remember (eval_expr e2 rho).
  dec_enc. rewrite DE. clear DE. subst.
  eapply load_cast; eauto.
}
destruct H11 as [m' [H11 AM]].
exists (store_juicy_mem _ _ _ _ _ _ H11).
exists (te);  exists rho; split3; auto.
subst; simpl; auto.
rewrite level_store_juicy_mem. apply age_level; auto.
split; auto.
split.
split3; auto.
generalize (eval_expr_relate _ _ _ _ _ e2 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC4)); intro.
spec H2; [ assumption | ].
rewrite <- (age_jm_dry Hage) in H2, He1.
econstructor; try eassumption.
unfold tc_lvalue in TC1. simpl in TC1.
auto.
instantiate (1:=(force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm)))).
rewrite (age_jm_dry Hage).
rewrite cop2_sem_cast'; auto.
2: eapply typecheck_expr_sound; eauto.
eapply cast_exists; eauto. destruct TC4; auto.
eapply Clight.assign_loc_value.
apply Hmode.
unfold tc_lvalue in TC1. simpl in TC1.
auto.
unfold Mem.storev.
simpl m_dry.
rewrite (age_jm_dry Hage).
auto.
apply (resource_decay_trans _ (nextblock (m_dry jm1)) _ (m_phi jm1)).
rewrite (age_jm_dry Hage); lia.
apply (age1_resource_decay _ _ Hage).
apply resource_nodecay_decay.
apply juicy_store_nodecay.
{intros.
 clear - H11' H2 WS.
 destruct H11' as [phi1 [phi2 [? [? ?]]]].
 destruct H0 as [bl [_ ?]]. specialize  (H0 (b0,z)).
 hnf in H0. rewrite if_true in H0 by (split; auto; lia).
 destruct H0. hnf in H0.
 apply (resource_at_join _ _ _ (b0,z)) in H.
 rewrite H0 in H.
 inv H; simpl; apply join_writable01 in RJ; auto;
 unfold perm_of_sh; rewrite if_true by auto; if_tac; constructor.
}
rewrite level_store_juicy_mem. split; [apply age_level; auto|].
simpl. unfold inflate_store; rewrite ghost_of_make_rmap.
apply age1_ghost_of, age_jm_phi; auto.
split.
2 : { eapply (corable_core _ (m_phi jm1)), pred_hereditary; eauto; [|apply age_jm_phi; auto].
      symmetry.
      forget (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))) as v.
      apply rmap_ext.
      do 2 rewrite level_core.
      rewrite <- level_juice_level_phi; rewrite level_store_juicy_mem.
      reflexivity.
      intro loc.
      unfold store_juicy_mem. simpl.
      rewrite <- core_resource_at. unfold inflate_store.
      rewrite resource_at_make_rmap. rewrite <- core_resource_at.
      case_eq (m_phi jm1 @ loc); intros; auto.
      destruct k0; simpl resource_fmap; repeat rewrite core_YES; auto.
      simpl.
      rewrite !ghost_of_core.
      unfold inflate_store; rewrite ghost_of_make_rmap; auto.
}
rewrite sepcon_comm.
rewrite sepcon_assoc.
eapply sepcon_derives; try apply AM; auto.
unfold mapsto.
destruct TC4 as [TC4 _].

rewrite Hmode.
rewrite He1'.
*
rewrite cop2_sem_cast'; auto.
2: eapply typecheck_expr_sound; eauto.
rewrite NONVOL.
rewrite if_true by auto.
apply orp_right1.
apply andp_right.
intros ? ?.
eapply tc_val_sem_cast; eauto.
intros ? ?. apply H2.
*
intros ? ?.
destruct H2 as (? & H2 & ?).
destruct (nec_join2 H6 H2) as [w2' [w' [? [? ?]]]].
eapply pred_upclosed; eauto.
exists w2'; exists w'; split3; auto; eapply pred_nec_hereditary; eauto.
Qed.

Definition numeric_type (t: type) : bool :=
match t with
| Tint IBool _ _ => false
| Tint _ _ _ => true
| Tlong _ _ => true
| Tfloat _ _ => true
| _ => false
end.

Lemma semax_store_union_hack:
     forall
         (Delta : tycontext) (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : LiftEnviron mpred),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax Espec Delta
         (fun rho =>
           |> (tc_lvalue Delta e1 rho && tc_expr Delta (Ecast e2 (typeof e1)) rho &&
              ( (mapsto_ sh (typeof e1) (eval_lvalue e1 rho) && mapsto_ sh t2 (eval_lvalue e1 rho))
               * P rho)))
         (Sassign e1 e2)
         (normal_ret_assert
            (fun rho => (EX v':val,
              andp (!! (decode_encode_val  (force_val (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho
))) ch ch' v'))
              (mapsto sh t2 (eval_lvalue e1 rho) v' * P rho)))).
Proof.
intros until P. intros NT AM0 AM' OK WS.
assert (SZ := decode_encode_val_size _ _ OK).
apply semax_pre with
  (fun rho : environ =>
   EX v3: val,
      |> tc_lvalue Delta e1 rho && |> tc_expr Delta (Ecast e2 (typeof e1)) rho &&
      |> ((mapsto sh (typeof e1) (eval_lvalue e1 rho) v3 && mapsto sh t2 (eval_lvalue e1 rho) v3) * P rho)).
intro. apply andp_left2.
unfold mapsto_.
apply exp_right with Vundef.
repeat rewrite later_andp; auto.
apply extract_exists_pre; intro v3.
apply semax_straight_simple; auto.
intros jm jm1 Delta' ge ve te rho k F f TS [TC1 TC2] TC4 Hcl Hge Hage [H0 H0'] HGG'.
specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
assert (typecheck_environ Delta rho) as TC.
{ destruct TC4. eapply typecheck_environ_sub; eauto. }
pose proof TC1 as TC1'.
pose proof TC2 as TC2'.
apply (tc_lvalue_sub _ _ _ TS) in TC1'; [| auto].
apply (tc_expr_sub _ _ _ TS) in TC2'; [| auto].
unfold tc_expr in TC2, TC2'; simpl in TC2, TC2'.
rewrite denote_tc_assert_andp in TC2, TC2'.
simpl in TC2,TC2'; super_unfold_lift.
destruct TC2 as [TC2 TC3].
destruct TC2' as [TC2' TC3'].
apply later_sepcon2 in H0.
specialize (H0 _ (age_laterR (age_jm_phi Hage))).
pose proof I.
destruct H0 as [?w [?w [? [? [?w [?w [H3 [H4 H5]]]]]]]].
destruct H4 as [H4 H4x].
unfold mapsto in H4.
revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
rename H2 into Hmode.
rewrite Hmode in AM0; inversion AM0; clear AM0; subst m.
destruct (eval_lvalue_relate _ _ _ _ _ e1 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC4)) as [b0 [i [He1 He1']]]; auto.
rewrite He1' in *.
destruct (join_assoc H3 (join_comm H0)) as [?w [H6 H7]].
destruct (type_is_volatile (typeof e1)) eqn:NONVOL; try contradiction.
rewrite if_true in H4 by auto.
assert (exists v, address_mapsto ch v
             sh
        (b0, Ptrofs.unsigned i) w1)
       by (destruct H4 as [[H4' H4] |[? [? ?]]]; eauto).
assert (H77: (align_chunk ch' | Ptrofs.unsigned i) /\ type_is_volatile t2 = false). {
  clear - H4x AM'.
  unfold mapsto  in H4x.
  rewrite AM' in H4x.
  destruct(type_is_volatile t2); try contradiction. split; auto.
  if_tac in H4x.
  destruct H4x as [[_ ?] | [_ ?]].
  rewrite address_mapsto_align in H0; destruct H0 as [_ H0]; simpl in H0; auto.
  destruct H0 as [? ?].
  rewrite address_mapsto_align in H0; destruct H0 as [_ H0]; simpl in H0; auto.
  destruct H4x as [[_ ?] _]. auto.
}
clear H4x.
clear v3 H4; destruct H2 as [v3 H4].

assert (H11': (res_predicates.address_mapsto ch v3 sh
        (b0, Ptrofs.unsigned i) * TT)%pred (m_phi jm1))
 by (exists w1; exists w3; split3; auto).
assert (H11: (res_predicates.address_mapsto ch v3  sh
        (b0, Ptrofs.unsigned i) * exactly w3)%pred (m_phi jm1)).
{ exists w1; exists w3; split3; auto.
  hnf; eauto. }
apply address_mapsto_can_store'
   with (ch':=ch') (v':=((force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))))) in H11;
  auto.
2: apply H77.
(*
2: {
  unfold typecheck_store in *.
  destruct TC4 as [TC4 _].
  simpl in TC2'. apply typecheck_expr_sound in TC2'; auto.
  remember (eval_expr e2 rho).
  dec_enc. rewrite DE. clear DE. subst.
  eapply load_cast; eauto.
}
*)
destruct H11 as [m' [H11 AM]].
exists (store_juicy_mem _ _ _ _ _ _ H11).
exists (te);  exists rho; split3; auto.
subst; simpl; auto.
rewrite level_store_juicy_mem. apply age_level; auto.
split; auto.
split.
split3; auto.
generalize (eval_expr_relate _ _ _ _ _ e2 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC4)); intro.
spec H2; [ assumption | ].
rewrite <- (age_jm_dry Hage) in H2, He1.
econstructor; try eassumption.
unfold tc_lvalue in TC1. simpl in TC1.
auto.
instantiate (1:=(force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm)))).
rewrite (age_jm_dry Hage).
rewrite cop2_sem_cast'; auto.
2: eapply typecheck_expr_sound; eauto.
eapply cast_exists; eauto. destruct TC4; auto.
eapply Clight.assign_loc_value.
apply Hmode.
unfold tc_lvalue in TC1. simpl in TC1.
auto.
unfold Mem.storev.
simpl m_dry.
rewrite (age_jm_dry Hage).
auto.
apply (resource_decay_trans _ (nextblock (m_dry jm1)) _ (m_phi jm1)).
rewrite (age_jm_dry Hage); lia.
apply (age1_resource_decay _ _ Hage).
apply resource_nodecay_decay.
apply juicy_store_nodecay.
{intros.
 clear - H11' H2 WS.
 destruct H11' as [phi1 [phi2 [? [? ?]]]].
 destruct H0 as [bl [_ ?]]. specialize  (H0 (b0,z)).
 hnf in H0. rewrite if_true in H0 by (split; auto; lia).
 destruct H0. hnf in H0.
 apply (resource_at_join _ _ _ (b0,z)) in H.
 rewrite H0 in H.
 inv H; simpl; apply join_writable01 in RJ; auto;
 unfold perm_of_sh; rewrite if_true by auto; if_tac; constructor.
}
rewrite level_store_juicy_mem. split; [apply age_level; auto|].
simpl. unfold inflate_store; rewrite ghost_of_make_rmap.
apply age1_ghost_of, age_jm_phi; auto.
split.
2 : {
      eapply (corable_core _ (m_phi jm1)), pred_hereditary; eauto; [|apply age_jm_phi; auto].
      symmetry.
      forget (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))) as v.
      apply rmap_ext.
      do 2 rewrite level_core.
      rewrite <- level_juice_level_phi; rewrite level_store_juicy_mem.
      reflexivity.
      intro loc.
      unfold store_juicy_mem. simpl.
      rewrite <- core_resource_at. unfold inflate_store.
      rewrite resource_at_make_rmap. rewrite <- core_resource_at.
      case_eq (m_phi jm1 @ loc); intros; auto.
      destruct k0; simpl resource_fmap; repeat rewrite core_YES; auto.
      simpl.
      rewrite !ghost_of_core.
      unfold inflate_store; rewrite ghost_of_make_rmap; auto.
}

assert (TCv: tc_val (typeof e1)  (force_val (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho)))).
  eapply tc_val_sem_cast; eauto.
erewrite <- cop2_sem_cast' in *; try eassumption;
   try (eapply typecheck_expr_sound; eauto).
forget (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))) as v.
rewrite sepcon_comm.
destruct  (load_store_similar' _ _ _ _ _ _ H11 ch') as [v' [? ?]].
auto.
auto.
apply H77.
rewrite exp_sepcon1.
exists v'.
rewrite prop_true_andp by auto.
rewrite sepcon_assoc.
eapply sepcon_derives; try apply AM; auto.
unfold mapsto.
destruct TC4 as [TC4 _].

rewrite AM'.
rewrite He1'.
*
apply exp_left; intro v''.
apply prop_andp_left; intro.
pose proof (decode_encode_val_fun _ _  OK _ _ _  H8 H9).
subst v''; clear H9.
rewrite (proj2 H77).
rewrite if_true by auto.
apply orp_right1.
apply andp_right; auto.
intros ? ?.
simpl.
clear - H8 NT OK Hmode AM' TCv.
rewrite andb_true_iff in NT; destruct NT as [NT NT'].
destruct ch, ch'; try contradiction OK;
destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv NT; inv Hmode;
destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv NT'; inv AM';
destruct v; simpl in H8; subst; try contradiction;
try apply I;
try (apply tc_val_Vundef in TCv; contradiction);
match goal with
 | |- context [Int.sign_ext ?n] => apply (sign_ext_range' n); compute; split; congruence
 | |- context [Int.zero_ext ?n] => apply (zero_ext_range' n); compute; split; congruence
 | |- _ => idtac
end.
*
intros ? ?.
clear - H9 H6 H1 H5.
destruct H9 as (? & H9 & ?).
destruct (nec_join2 H6 H9) as [w2' [w' [? [? ?]]]].
eapply pred_upclosed; eauto.
exists w2'; exists w'; split3; auto; eapply pred_nec_hereditary; eauto.
Qed.


End extensions.
