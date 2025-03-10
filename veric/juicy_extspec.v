Require Import VST.veric.juicy_base.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.shares.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.juicy_mem. (*VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.*)

Require Import VST.veric.ghost_PCM. (*avoids doing Require Import VST.veric.initial_world.*)
Require Import VST.veric.own.
Require Import VST.veric.invariants.
Require Import VST.veric.tycontext.

Require Import VST.veric.age_to_resource_at.

Local Open Scope nat_scope.
Local Open Scope pred.

Record juicy_ext_spec (Z: Type) := {
  JE_spec:> external_specification juicy_mem external_function Z;
  JE_pre_hered: forall e t ge_s typs args z, hereditary age (ext_spec_pre JE_spec e t ge_s typs args z);
  JE_pre_ext: forall e t ge_s typs args z a a', ext_order a a' ->
    joins (ghost_of (m_phi a')) (Some (ext_ref z, NoneP) :: nil) ->
    ext_spec_pre JE_spec e t ge_s typs args z a ->
    ext_spec_pre JE_spec e t ge_s typs args z a';
  JE_post_hered: forall e t ge_s tret rv z, hereditary age (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_post_ext: forall e t ge_s tret rv z, hereditary ext_order (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_exit_hered: forall rv z, hereditary age (ext_spec_exit JE_spec rv z);
  JE_exit_ext: forall rv z, hereditary ext_order (ext_spec_exit JE_spec rv z)
}.

Class OracleKind := {
  OK_ty : Type;
  OK_spec: juicy_ext_spec OK_ty
}.

(*! The void ext_spec *)
Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False)
      (fun ef Hef ge tys vl m z => False)
      (fun ef Hef ge ty vl m z => False)
      (fun rv m z => False).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _ _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
Defined.

Definition j_initial_core {C} (csem: @CoreSemantics C mem)
     (n: nat) (m: juicy_mem) (q: C) (m': juicy_mem) (v: val) (args: list val) 
     : Prop :=
  m' = m /\
  semantics.initial_core csem n (m_dry m) q (m_dry m') v args.

Definition j_at_external {C} (csem: @CoreSemantics C mem)
   (q: C) (jm: juicy_mem) : option (external_function * list val) :=
   semantics.at_external csem q (m_dry jm).

Definition j_after_external {C} (csem: @CoreSemantics C mem)
    (ret: option val) (q: C) (jm: juicy_mem) :=
   semantics.after_external csem ret q (m_dry jm).

Definition jstep {C} (csem: @CoreSemantics C mem)
  (q: C) (jm: juicy_mem) (q': C) (jm': juicy_mem) : Prop :=
 corestep csem q (m_dry jm) q' (m_dry jm') /\ 
 resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
 level jm = S (level jm') /\
 ghost_of (m_phi jm') = ghost_approx jm' (ghost_of (m_phi jm)).

Definition j_halted {C} (csem: @CoreSemantics C mem)
       (c: C) (i: int): Prop :=
     halted csem c i.

Lemma jstep_not_at_external {C} (csem: @CoreSemantics C mem):
  forall m q m' q', jstep csem q m q' m' -> at_external csem q (m_dry m) = None.
Proof.
  intros.
  destruct H as (? & ? & ? & ?). eapply corestep_not_at_external; eauto.
Qed.

Lemma jstep_not_halted  {C} (csem: @CoreSemantics C mem):
  forall m q m' q' i, jstep csem q m q' m' -> ~j_halted csem q i.
Proof.
  intros. destruct H as (? & ? & ? & ?). eapply corestep_not_halted; eauto.
Qed.

(*Lenb: removed here. To be moved a more CLight-specific place
Record jm_init_package: Type := {
  jminit_m: Memory.mem;
  jminit_prog: program;
  jminit_G: tycontext.funspecs;
  jminit_lev: nat;
  jminit_init_mem: Genv.init_mem jminit_prog = Some jminit_m;
  jminit_defs_no_dups:   list_norepet (prog_defs_names jminit_prog);
  jminit_fdecs_match: match_fdecs (prog_funct jminit_prog) jminit_G
}.

Definition init_jmem {G} (ge: G) (jm: juicy_mem) (d: jm_init_package) :=
  jm = initial_jm (jminit_prog d) (jminit_m d) (jminit_G d) (jminit_lev d)
         (jminit_init_mem d) (jminit_defs_no_dups d) (jminit_fdecs_match d).
*)
Definition juicy_core_sem
  {C} (csem: @CoreSemantics C mem) :
   @CoreSemantics C juicy_mem :=
  @Build_CoreSemantics _ juicy_mem
    (j_initial_core csem)
    (j_at_external csem)
    (j_after_external csem)
    (j_halted csem)
    (jstep csem)
    (jstep_not_halted csem)
    (jstep_not_at_external csem)
(*  (j_at_external_halted_excl csem)*).

Section upd_exit.
  Context {Z : Type}.
  Variable spec : juicy_ext_spec Z.

  Definition upd_exit' (Q_exit : option val -> Z -> juicy_mem -> Prop) :=
  {| ext_spec_type := ext_spec_type spec
   ; ext_spec_pre := ext_spec_pre spec
   ; ext_spec_post := ext_spec_post spec
   ; ext_spec_exit := Q_exit |}.

  Definition upd_exit'' (ef : external_function) (x : ext_spec_type spec ef) ge :=
    upd_exit' (ext_spec_post spec ef x ge (sig_res (ef_sig ef))).

  Program Definition upd_exit {ef : external_function} (x : ext_spec_type spec ef) ge :=
    Build_juicy_ext_spec _ (upd_exit'' _ x ge) _ _ _.
  Next Obligation. intros. eapply JE_pre_hered; eauto. Qed.
  Next Obligation. intros. eapply JE_pre_ext; eauto. Qed.
  Next Obligation. intros. eapply JE_post_hered; eauto. Qed.
End upd_exit.

Obligation Tactic := Tactics.program_simpl.

Program Definition juicy_mem_op (P : pred rmap) : pred juicy_mem :=
  fun jm => P (m_phi jm).
 Next Obligation.
  split; repeat intro.
  apply age1_juicy_mem_unpack in H.
  destruct H.
  eapply pred_hereditary; eauto.

  destruct H; eapply pred_upclosed; eauto.
 Qed.

Lemma age_resource_decay:
   forall b jm1 jm2 jm1' jm2',
        resource_decay b jm1 jm2 ->
        age jm1 jm1' -> age jm2 jm2' ->
        level jm1 = S (level jm2) ->
        resource_decay b jm1' jm2'.
Proof.
  unfold resource_decay; intros.
  rename H2 into LEV.
  destruct H as [H' H].
  split.
  {
    clear H.
    apply age_level in H0; apply age_level in H1.
    rewrite H0 in *; rewrite H1 in *. inv LEV. rewrite H2.
    clear. forget (level jm2') as n. lia.
  }
  intro l.
  specialize (H l).
  destruct H.
  split.
  {
    intro.
    specialize (H H3).
    erewrite <- necR_NO; eauto.  constructor 1; auto.
  }
  destruct H2 as [?|[?|[?|?]]].
  + left.
    clear H. unfold age in *.
    rewrite (age1_resource_at _ _ H0 l (jm1 @ l)); [ | symmetry; apply resource_at_approx].
    rewrite (age1_resource_at _ _ H1 l (jm2 @ l)); [ | symmetry; apply resource_at_approx].
    rewrite <- H2.
    rewrite resource_fmap_fmap.
    rewrite resource_fmap_fmap.
    f_equal.
    - change R.approx with approx.
      rewrite approx_oo_approx'; [rewrite approx_oo_approx'; auto |].
      * apply age_level in H0; apply age_level in H1.
        unfold rmap  in *;
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
      * apply age_level in H0; apply age_level in H1.
        unfold rmap in *.
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
    - change R.approx with approx.
      rewrite approx'_oo_approx; [rewrite approx'_oo_approx; auto |].
      * apply age_level in H0; apply age_level in H1.
        unfold rmap  in *;
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
      * apply age_level in H0; apply age_level in H1.
        unfold rmap in *.
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
  + right.
    destruct H2 as [sh [wsh [v [v' [? ?]]]]].
    left; exists sh, wsh, v,v'.
    split.
    - apply age_level in H1.
      unfold rmap in *.
      forget (@level R.rmap R.ag_rmap jm2) as j2.
      forget (@level R.rmap R.ag_rmap jm2') as j2'. subst j2.
      clear - H2 H0 LEV.
      revert H2; case_eq (jm1 @ l); intros; inv H2.
      pose proof (necR_YES jm1 jm1' l sh r (VAL v) p (rt_step _ _ _ _ H0) H).
      rewrite H1.
      simpl. rewrite preds_fmap_fmap.
      apply age_level in H0.
      rewrite approx_oo_approx'.
        2: rewrite H0 in *; inv LEV; lia.
      rewrite approx'_oo_approx.
        2: rewrite H0 in *; inv LEV; lia.
      f_equal. apply proof_irr.
      rewrite H5.
      rewrite <- (approx_oo_approx' j2' (S j2')) at 1 by auto.
      rewrite <- (approx'_oo_approx j2' (S j2')) at 2 by auto.
      rewrite <- preds_fmap_fmap; rewrite H5. rewrite preds_fmap_NoneP. auto. 
    - pose proof (age1_YES _ _ l sh (writable0_readable wsh) (VAL v') H1).
      rewrite H4 in H3. auto.
  + destruct H2 as [? [v ?]]; right; right; left.
    split; auto. exists v.   apply (age1_YES _ _ l _ _ _ H1) in H3. auto.
  + right; right; right.
    destruct H2 as [v [pp [? ?]]]. exists v. econstructor; split; auto. 
    pose proof (age1_resource_at _ _ H0 l (YES Share.top readable_share_top(VAL v) pp)).
    rewrite H4.
    simpl. reflexivity.
    rewrite <- (resource_at_approx jm1 l).
    rewrite H2. reflexivity.
    assert (necR jm2 jm2'). apply laterR_necR. constructor. auto.
    apply (necR_NO _ _ l Share.bot bot_unreadable H4). auto.
Qed.

Lemma necR_PURE' phi0 phi k p adr :
  necR phi0 phi ->
  phi @ adr = PURE k p ->
  (*a stronger theorem is possible -- this one doesn't relate p, pp*)
  exists pp, phi0 @ adr = PURE k pp.
Proof.
  intros Hnec H.
  case_eq (phi0 @ adr). 
  { intros. eapply necR_NO in Hnec; try eassumption. 
    rewrite Hnec in H0. rewrite H0 in H. congruence. }
  { intros. eapply necR_YES in Hnec; eauto. rewrite Hnec in H. congruence. }
  { generalize (necR_level _ _ Hnec); intros Hlev.
    intros. eapply necR_PURE in Hnec; eauto.
    rewrite Hnec in H. inversion H. subst. eexists. eauto. }
Qed.

Definition jm_update m m' := m_dry m' = m_dry m /\ level m' = level m /\
  resource_at (m_phi m') = resource_at (m_phi m).

Lemma jm_update_age: forall m1 m2 m1', jm_update m1 m2 -> age m1 m1' ->
  exists m2', jm_update m1' m2' /\ age m2 m2'.
Proof.
  intros ??? (? & ? & ?) Hage.
  pose proof (age_level _ _ Hage).
  destruct (levelS_age m2 (level m1')) as (m2' & Hage2 & ?); [lia|].
  exists m2'; repeat split; auto.
  - rewrite <- (age_jm_dry Hage), <- (age_jm_dry Hage2); auto.
  - extensionality l.
    apply age_jm_phi in Hage; apply age_jm_phi in Hage2.
    rewrite (age_resource_at Hage), (age_resource_at Hage2).
    rewrite <- !level_juice_level_phi; congruence.
Qed.

Definition has_ext {Z} (ora : Z) : mpred.mpred := @own (ext_PCM _) 0 (Some (Tsh, Some ora), None) NoneP.

Definition jm_bupd {Z} (ora : Z) P m := forall C : ghost,
  (* use the external state to restrict the ghost moves *)
  join_sub (Some (ext_ref ora, NoneP) :: nil) C ->
  joins (ghost_of (m_phi m)) (ghost_approx m C) ->
  exists m' : juicy_mem, joins (ghost_of (m_phi m')) ((ghost_approx m) C) /\
    jm_update m m' /\ P m'.

Lemma jm_bupd_intro: forall {Z} (ora : Z) (P : juicy_mem -> Prop) m, P m -> jm_bupd ora P m.
Proof.
  repeat intro.
  eexists; split; eauto; repeat split; auto.
Qed.

Lemma jm_bupd_mono : forall {Z} (ora : Z) (P1 P2 : juicy_mem -> Prop) m, jm_bupd ora P1 m ->
  (forall m', level m' <= level m -> P1 m' -> P2 m') -> jm_bupd ora P2 m.
Proof.
  intros ?????? Hmono.
  intros ? HC J.
  destruct (H _ HC J) as (? & ? & ? & ?); eauto.
  assert (level x = level m) by (unfold jm_update in *; tauto).
  eexists; split; eauto; split; auto.
  apply Hmono; auto.
  replace (level x) with (level m); reflexivity.
Qed.

Lemma ext_join_approx : forall {Z} (z : Z) n g,
  joins g (Some (ghost_PCM.ext_ref z, NoneP) :: nil) ->
  joins (ghost_fmap (approx n) (approx n) g) (Some (ghost_PCM.ext_ref z, NoneP) :: nil).
Proof.
  intros.
  destruct H.
  change (Some (ghost_PCM.ext_ref z, NoneP) :: nil) with
    (ghost_fmap (approx n) (approx n) (Some (ghost_PCM.ext_ref z, NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
Qed.

Lemma ext_join_sub_approx : forall {Z} (z : Z) n g,
  join_sub (Some (ghost_PCM.ext_ref z, NoneP) :: nil) g ->
  join_sub (Some (ghost_PCM.ext_ref z, NoneP) :: nil) (ghost_fmap (approx n) (approx n) g).
Proof.
  intros.
  destruct H.
  change (Some (ghost_PCM.ext_ref z, NoneP) :: nil) with
    (ghost_fmap (approx n) (approx n) (Some (ghost_PCM.ext_ref z, NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
Qed.

Lemma ext_join_unapprox : forall {Z} (z : Z) n g,
  joins (ghost_fmap (approx n) (approx n) g) (Some (ghost_PCM.ext_ref z, NoneP) :: nil) ->
  joins g (Some (ghost_PCM.ext_ref z, NoneP) :: nil).
Proof.
  intros.
  destruct H as (g' & J).
  destruct g; [eexists; constructor|].
  inv J.
  exists (a3 :: g); repeat constructor.
  destruct o; inv H4; constructor.
  destruct p; inv H1; constructor; simpl in *; auto.
  destruct p; simpl in *.
  inv H0.
  inv H1.
  inj_pair_tac.
  constructor; auto.
  unfold NoneP; f_equal; auto.
Qed.

Lemma jm_bupd_ext : forall {Z} (ora : Z) (P : juicy_mem -> Prop) m m', jm_bupd ora P m ->
  ext_order m m' ->
  (forall a b, level a = level m -> ext_order a b -> joins (ghost_of (m_phi b)) (Some (ext_ref ora, NoneP) :: nil) ->
      P a -> P b) ->
  jm_bupd ora P m'.
Proof.
  intros ????? H [? Hext] Hclosed ? Hora H1.
  apply rmap_order in Hext as (Hl & Hr & [? J]).
  destruct H1 as [d J'].
  destruct (join_assoc J J') as (c' & ? & Jc').
  eapply ghost_fmap_join in Jc'; rewrite ghost_of_approx in Jc'.
  destruct (H c') as (m'' & Jm'' & (? & Hl'' & ?) & ?).
  { eapply ext_join_sub_approx in Hora.
    eapply join_sub_trans; eauto.
    eexists; eauto. }
  { rewrite level_juice_level_phi; eauto. }
  assert (level m'' = level m') as Hl'.
  { rewrite <- !level_juice_level_phi in *; congruence. }
  exists m''; repeat split; auto; try congruence.
  eapply join_sub_joins'; eauto.
  { apply join_sub_refl. }
  eapply ghost_fmap_join in H1; rewrite ghost_fmap_fmap, 2approx_oo_approx in H1.
  rewrite <- Hl'', Hl'; eexists; eauto.
Qed.

(*(* Just like we reserve ghost name 0 for the external ghost, we reserve 1-3 for invariants/world satisfaction.
  Presumably we'll have to prove that this isn't vacuous somewhere in the soundness proof.
  We could delay the instantiation and be generic in inv_names, but since we know we'll always need it and we get to allocate it
  before the program starts, I don't see any reason to hold off. *)
#[(*export, after Coq 8.13*)global] Instance inv_names : invG := { g_inv := 1%nat; g_en := 2%nat; g_dis := 3%nat}.

Polymorphic Definition jm_fupd {Z} (ora : Z) (E1 E2 : Ensembles.Ensemble gname) P m :=
  forall m' w z, necR m m' -> join (m_phi m') w (m_phi z) -> app_pred (wsat * ghost_set g_en E1) w ->
  jm_bupd ora (fun z2 => level z2 = 0 \/ exists m2 w2, join (m_phi m2) w2 (m_phi z2) /\
    app_pred (wsat * ghost_set g_en E2) w2 /\ P m2) z.

Polymorphic Lemma jm_fupd_intro: forall {Z} (ora : Z) E (P : juicy_mem -> Prop) m (HP : forall a b, P a -> necR a b -> P b),
  P m -> jm_fupd ora E E P m.
Proof.
  intros.
  intros ??????.
  apply jm_bupd_intro; eauto 7.
Qed.

Polymorphic Lemma jm_fupd_age : forall {Z} (ora : Z) E1 E2 (P : juicy_mem -> Prop) m m', jm_fupd ora E1 E2 P m ->
  age m m' -> jm_fupd ora E1 E2 P m'.
Proof.
  intros.
  intros ??????.
  eapply H; [|eauto | eauto].
  eapply necR_trans; [|eauto].
  constructor; auto.
Qed.

Polymorphic Lemma jm_fupd_mono : forall {Z} (ora : Z) E1 E2 (P1 P2 : juicy_mem -> Prop) m, jm_fupd ora E1 E2 P1 m ->
  (forall m', level m' <= level m -> P1 m' -> P2 m') -> jm_fupd ora E1 E2 P2 m.
Proof.
  intros ???????? Hmono.
  intros ??? Hlater J HW.
  eapply H in HW; eauto.
  eapply jm_bupd_mono; eauto.
  intros ?? [|(? & ? & J2 & ? & ?)]; eauto.
  right; do 3 eexists; eauto; split; auto.
  apply Hmono; auto.
  apply necR_level in Hlater.
  apply join_level in J as [Hl ?].
  rewrite <- !level_juice_level_phi in Hl.
  apply join_level in J2 as [Hl2 ?].
  rewrite <- !level_juice_level_phi in Hl2.
  lia.
Qed.*)

Section juicy_safety.
  Context {G C Z:Type}.
  Context {genv_symb: G -> injective_PTree block}.
  Context (Hcore:@CoreSemantics C mem).
  Variable (Hspec : juicy_ext_spec Z).
  Variable ge : G.

  Definition Hrel n' m m' :=
    n' = level m' /\
    (level m' < level m)%nat /\
    pures_eq (m_phi m) (m_phi m').

  Inductive jsafeN_:
    nat -> Z -> C -> juicy_mem -> Prop :=
  | jsafeN_0: forall z c m, jsafeN_ O z c m
  | jsafeN_step:
      forall n z c m c' m',
      jstep Hcore c m c' m' ->
      jm_bupd z (jsafeN_ n z c') m' ->
      jsafeN_ (S n) z c m
  | jsafeN_external:
      forall n z c m e args x,
      j_at_external Hcore c m = Some (e,args) ->
      ext_spec_pre Hspec e x (genv_symb ge) (sig_args (ef_sig e)) args z m ->
      (forall ret m' z' n'
         (Hargsty : Val.has_type_list args (sig_args (ef_sig e)))
         (Hretty : Builtins0.val_opt_has_rettype  ret (sig_res (ef_sig e))),
         (n' <= n)%nat ->
         Hrel n' m m' ->
         ext_spec_post Hspec e x (genv_symb ge) (sig_res (ef_sig e)) ret z' m' ->
         exists c',
           semantics.after_external Hcore ret c (m_dry m') = Some c' /\
           jm_bupd z' (jsafeN_ n' z' c') m') ->
      jsafeN_ (S n) z c m
  | jsafeN_halted:
      forall n z c m i,
      semantics.halted Hcore c i ->
      ext_spec_exit Hspec (Some (Vint i)) z m ->
      jsafeN_ n z c m.

  Lemma jsafe_downward1 :
    forall n c m z,
      jsafeN_ (S n) z c m -> jsafeN_ n z c m.
  Proof.
    induction n. econstructor; eauto.
    intros c m z H. inv H.
    + econstructor; eauto.
      eapply jm_bupd_mono; eauto; simpl; intros.
    + eapply jsafeN_external; eauto.
    + eapply jsafeN_halted; eauto.
  Qed.

  Lemma jsafe_downward :
    forall n n' c m z,
      Peano.le n' n ->
      jsafeN_ n z c m -> jsafeN_ n' z c m.
  Proof.
    do 6 intro. revert c m z. induction H; auto.
    intros. apply IHle. apply jsafe_downward1. auto.
  Qed.

Lemma make_join_ext : forall (ora : Z) a c n,
  join_sub (Some (ext_ref ora, NoneP) :: nil) c ->
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  join_sub (Some (ext_ref ora, NoneP) :: nil) (make_join a c).
Proof.
  destruct a; auto; simpl.
  intros ?? [? HC] [? J].
  inv J.
  { destruct c; inv H1; inv HC. }
  destruct c; inv H1.
  inv H2.
  { destruct o; inv H0; inv HC.
    * eexists; constructor; constructor.
    * eexists; constructor; eauto; constructor. }
  { destruct o0; inv H1; inv HC.
    inv H3. }
  destruct o as [[]|], o0 as [[]|]; inv H; inv H0.
  destruct a0; inv H1; simpl in *.
  inv H0.
  assert (@ghost.valid (ext_PCM Z) (None, None)) as Hv.
  { simpl; auto. }
  inv HC.
  - eexists; constructor; constructor.
    destruct p; inv H1; inj_pair_tac.
    instantiate (1 := (existT _ (ext_PCM Z) (exist _ _ Hv), _)); repeat constructor; simpl.
    rewrite <- H0; auto.
  - inv H6.
    + destruct p; inv H1; inj_pair_tac.
      eexists; constructor; constructor.
      instantiate (1 := (existT _ (ext_PCM Z) (exist _ _ Hv), _)); repeat constructor; simpl.
      rewrite <- H0; auto.
    + destruct a0; inv H5; simpl in *.
      inv H2.
      destruct p; inv H1; inj_pair_tac.
      eexists; constructor; constructor.
      instantiate (1 := (_, _)); constructor; eauto; simpl.
      constructor; eauto.
      unfold NoneP; f_equal.
      rewrite <- H1; auto.
Qed.

Lemma age_safe:
  forall jm jm0, age jm0 jm ->
  forall ora c,
   jsafeN_ (level jm0) ora c jm0 ->
   jsafeN_ (level jm) ora c jm.
Proof.
 intros. rename H into H2.
 rewrite (age_level _ _ H2) in H0.
   remember (level jm) as N.
   revert c jm0 jm HeqN H2 H0; induction N; intros.
   constructor.
 remember (S N) as SN.
   subst SN.
  inv H0.
  + pose proof (age_level _ _ H2).
   destruct H1 as (? & ? & ? & Hg).
   assert (level m' > 0) by lia.
   assert (exists i, level m' = S i).
   destruct (level m'). lia. eauto.
   destruct H6 as [i Hl'].
   symmetry in Hl'; pose proof (levelS_age _ _ Hl') as [jm1' []]; subst.
   econstructor.
   split.
   rewrite <- (age_jm_dry H2), <- (age_jm_dry H6); eauto.
   split.
   rewrite <- (age_jm_dry H2).
   eapply age_resource_decay; try eassumption; try apply age_jm_phi; auto.
   destruct (age1_juicy_mem_unpack _ _ H2); auto.
   destruct (age1_juicy_mem_unpack _ _ H6); auto.
   split.
   apply age_level in H6. rewrite <- H6.
   lia.
   rewrite (age1_ghost_of _ _ (age_jm_phi H6)), (age1_ghost_of _ _ (age_jm_phi H2)), Hg.
   rewrite H in H4; inv H4.
   rewrite !level_juice_level_phi; congruence.
    intros ? HC J.
   rewrite (age1_ghost_of _ _ (age_jm_phi H6)) in J.
   destruct (ghost_joins_approx _ _ _ J) as (J1 & HC1).
   rewrite <- (age_level _ _ (age_jm_phi H6)) in *.
   rewrite ghost_of_approx in J1.
   destruct (H3 (make_join (compcert_rmaps.R.ghost_of (m_phi m')) C0)) as (m'' & ? & Hupd & ?); auto.
   { eapply make_join_ext; eauto. }
   destruct (jm_update_age _ _ _ Hupd H6) as (jm1'' & Hupd1 & Hage1).
   exists jm1''; split.
   { rewrite (age1_ghost_of _ _ (age_jm_phi Hage1)).
     replace (level (m_phi jm1'')) with (level (m_phi jm1')); auto.
     destruct Hupd1 as (? & ? & ?); rewrite <- !level_juice_level_phi; auto. }
   split; auto.
   destruct Hupd1 as (? & ? & ?).
   eapply IHN; eauto; lia.
  + eapply jsafeN_external; [eauto | eapply JE_pre_hered; eauto |].
    { unfold j_at_external in *.
      rewrite <- (age_jm_dry H2); eauto. }
    intros.
    destruct (H4 ret m' z' n') as [c' [? ?]]; auto.
    - assert (level (m_phi jm) < level (m_phi jm0)).
      {
        apply age_level in H2.
        do 2 rewrite <-level_juice_level_phi.
        destruct H0.
        rewrite H2; lia.
      }
      destruct H0 as (?&?&?).
      split3; [auto | do 2 rewrite <-level_juice_level_phi in H6; lia |].
      split.
      * destruct H8 as [H8 _].
        unfold pures_sub in H8. intros adr. specialize (H8 adr).
        assert (Hage: age (m_phi jm0) (m_phi jm)) by (apply age_jm_phi; auto).
        case_eq (m_phi jm0 @ adr); auto.
        intros k p Hphi.
        apply age1_resource_at with (loc := adr) (r := PURE k p) in Hage; auto.
       ++ rewrite Hage in H8; rewrite  H8; simpl.
          f_equal. unfold preds_fmap. destruct p. f_equal.
          generalize (approx_oo_approx' (level m') (level jm)); intros H9.
          spec H9; [lia |].
          generalize (approx'_oo_approx (level m') (level jm)); intros H10.
          spec H10; [lia |].
          do 2 rewrite <-level_juice_level_phi.
          rewrite fmap_app.
          rewrite H9, H10; auto.
       ++ rewrite <-resource_at_approx, Hphi; auto.
      * intros adr. case_eq (m_phi m' @ adr); auto. intros k p Hm'.
        destruct H8 as [_ H8].
        specialize (H8 adr). rewrite Hm' in H8. destruct H8 as [pp H8].
        apply age_jm_phi in H2.
        assert (Hnec: necR (m_phi jm0) (m_phi jm)) by (apply rt_step; auto).
        eapply necR_PURE' in Hnec; eauto.
    - exists c'; split; auto.
  + unfold j_halted in *.
    eapply jsafeN_halted; eauto.
    eapply JE_exit_hered; eauto.
Qed.

Lemma resource_decay_resource : forall b x x' y, resource_decay b x x' ->
  level x = level y -> resource_at x = resource_at y ->
  exists y', resource_decay b y y' /\ level y' = level x' /\
    resource_at x' = resource_at y' /\ ghost_of y' = own.ghost_approx y' (ghost_of y).
Proof.
  intros.
  destruct (make_rmap (resource_at x') (own.ghost_approx (level x') (ghost_of y)) (level x')) as (y' & Hl & Hr & Hg).
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, !approx_oo_approx; reflexivity. }
  rewrite <- Hl in Hg.
  exists y'; split; [|repeat split; auto].
  unfold resource_decay in *.
  destruct H.
  rewrite Hr, <- H1, Hl, <- H0; auto.
Qed.

Lemma ext_safe:
  forall jm jm0, ext_order jm0 jm ->
  forall ora c,
   joins (ghost_of (m_phi jm)) (Some (ext_ref ora, NoneP) :: nil) ->
   jsafeN_ (level jm0) ora c jm0 ->
   jsafeN_ (level jm) ora c jm.
Proof.
  intros ????? Hext ?.
  remember (level jm0) as N.
  revert dependent c; revert dependent jm0; revert dependent jm; induction N; intros.
  { destruct H as [_ H].
    destruct (proj1 (rmap_order _ _) H) as (Hl & _ & _).
    rewrite level_juice_level_phi, <- Hl, <- level_juice_level_phi, <- HeqN; constructor. }
  destruct H as [Hdry H].
  destruct (proj1 (rmap_order _ _) H) as (Hl & Hr & Hg).
  inv H0.
  - destruct H2 as (? & ? & ? & Hg').
    rewrite Hdry in *.
    eapply resource_decay_resource in H1 as (? & Hdecay & ? & Hr' & Hg''); eauto.
    rewrite level_juice_level_phi, <- Hl, <- level_juice_level_phi, H2.
    symmetry in Hr'; destruct (juicy_mem_resource _ _ Hr') as (m'' & ? & Hdry'); subst.
    eapply jsafeN_step.
    + split; [rewrite Hdry'; eauto|].
      split; auto; split; auto.
      rewrite !level_juice_level_phi in *; congruence.
    + rewrite H2 in HeqN; inv HeqN.
      eapply jm_bupd_ext; eauto.
      * simpl; rewrite rmap_order; repeat split; auto.
        rewrite Hg', Hg'', level_juice_level_phi, H1.
        destruct Hg; eexists; apply ghost_fmap_join; eauto.
      * intros ?? Hl1 Hb ??. rewrite <- Hl1, (ext_level _ _ Hb). eauto.
  - rewrite level_juice_level_phi, <- Hl, <- level_juice_level_phi, <- HeqN.
    eapply jsafeN_external.
    + unfold j_at_external in *.
      rewrite <- Hdry; eauto.
    + eapply JE_pre_ext, H3; auto.
      split; auto.
    + intros.
      apply H4; auto.
      unfold Hrel in *.
      destruct H1 as (? & ? & ?); split; auto.
      split; [rewrite !level_juice_level_phi in *; lia|].
      unfold pures_eq, pures_sub in *.
      rewrite Hr; auto.
  - eapply jsafeN_halted; eauto.
    eapply JE_exit_ext; [|eauto].
    split; auto.
Qed.

Lemma jsafe_corestep_backward:
    forall c m c' m' n z,
    jstep Hcore c m c' m' ->
    jsafeN_ n z c' m' -> jsafeN_ (S n) z c m.
  Proof.
    intros; eapply jsafeN_step; eauto.
    intros; eexists; repeat split; eauto.
  Qed.

(*  Lemma jsafe_corestepN_forward:
    corestep_fun Hcore ->
    forall z c m c' m' n n0,
      semantics_lemmas.corestepN (juicy_core_sem Hcore) ge n0 c m c' m' ->
      jsafeN_ (n + S n0) z c m ->
      jm_bupd (jsafeN_ n z c') m'.
  Proof.
    intros.
    revert c m c' m' n H0 H1.
    induction n0; intros; auto.
    simpl in H0; inv H0.
    apply jm_bupd_intro.
    eapply jsafe_downward in H1; eauto. lia.
    simpl in H0. destruct H0 as [c2 [m2 [STEP STEPN]]].
    assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by lia.
    rewrite Heq in H1.
    eapply jsafe_corestep_forward in H1; eauto.
    specialize (H1 nil); spec H1.
    { eexists; simpl; erewrite <- ghost_core.
      apply join_comm, core_unit. }
    destruct H1 as (? & ? & ? & ?).
    eapply (IHn0 _ _ _ _ n).
  Qed.*)

  Lemma jsafe_step'_back2 :
    forall
      {ora st m st' m' n},
      jstep Hcore st m st' m' ->
      jsafeN_ (n-1) ora st' m' ->
      jsafeN_ n ora st m.
  Proof.
    intros.
    destruct n.
    constructor.
    simpl in H0. replace (n-0)%nat with n in H0.
    eapply jsafe_corestep_backward; eauto.
    lia.
  Qed.

  Lemma jsafe_corestepN_backward:
    forall z c m c' m' n n0,
      semantics_lemmas.corestepN (juicy_core_sem Hcore) n0 c m c' m' ->
      jsafeN_ (n - n0) z c' m' ->
      jsafeN_ n z c m.
  Proof.
    simpl; intros.
    revert c m c' m' n H H0.
    induction n0; intros; auto.
    simpl in H; inv H.
    solve[assert (Heq: (n = n - 0)%nat) by lia; rewrite Heq; auto].
    simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
    assert (H: jsafeN_ (n - 1 - n0) z c' m').
    eapply jsafe_downward in H0; eauto. lia.
    specialize (IHn0 _ _ _ _ (n - 1)%nat STEPN H).
    solve[eapply jsafe_step'_back2; eauto].
  Qed.

  Lemma convergent_controls_jsafe :
    forall m q1 q2,
      (j_at_external Hcore q1 m = j_at_external Hcore q2 m) ->
      (forall ret m q', semantics.after_external Hcore ret q1 m = Some q' ->
                      semantics.after_external Hcore ret q2 m = Some q') ->
      (semantics.halted Hcore q1 = semantics.halted Hcore q2) ->
      (forall q' m', jstep Hcore q1 m q' m' ->
                     jstep Hcore q2 m q' m') ->
      (forall n z, jsafeN_ n z q1 m -> jsafeN_ n z q2 m).
  Proof.
    intros. destruct n; simpl in *; try constructor.
    inv H3.
    + econstructor; eauto.
    + eapply jsafeN_external; eauto.
      rewrite <-H; eauto.
      intros ???? Hargsty Hretty ? H8 H9.
      specialize (H7 _ _ _ _ Hargsty Hretty H3 H8 H9).
      destruct H7 as [c' [? ?]].
      exists c'; split; auto.
    + eapply jsafeN_halted; eauto.
      rewrite <-H1; auto.
  Qed.

  Lemma wlog_jsafeN_gt0 : forall
    n z q m,
    (lt 0 n -> jsafeN_ n z q m) ->
    jsafeN_ n z q m.
  Proof.
    intros. destruct n. constructor.
    apply H. lia.
  Qed.

(*Lemma jm_fupd_intro': forall {Z} (ora : Z) E n z q m,
  jsafeN_ (min n (level m)) z q m -> jm_fupd ora E E (fun m' => jsafeN_ (min n (level m')) z q m') m.
Proof.
  intros; apply jm_fupd_intro, H.
  intros; eapply necR_safe; eauto.
Qed.*)

(*Polymorphic Lemma jm_fupd_age' : forall {Z} (ora : Z) E1 E2 z q m m', jm_fupd ora E1 E2 (fun jm => jsafeN_ (min (level m) (level jm)) z q jm) m ->
  age m m' -> jm_fupd ora E1 E2 (fun jm => jsafeN_ (min (level m') (level jm)) z q jm) m'.
Proof.
  intros.
  eapply jm_fupd_mono; [eapply jm_fupd_age; eauto|].
  simpl; intros.
  apply age_level in H0.
  rewrite !level_juice_level_phi in H0.
  rewrite min_r in * by lia; auto.
Qed.*)

End juicy_safety.

Lemma juicy_core_sem_preserves_corestep_fun
  {C} (csem: @CoreSemantics C mem) :
  corestep_fun csem ->
  corestep_fun (juicy_core_sem csem).
Proof.
  intros determinism jm q jm1 q1 jm2 q2 step1 step2.
  destruct step1 as [step1 [[ll1 rd1] [l1 g1]]].
  destruct step2 as [step2 [[ll2 rd2] [l2 g2]]].
  pose proof determinism _ _ _ _ _ _ step1 step2 as E.
  injection E as <- E; f_equal.
  apply juicy_mem_ext; auto.
  assert (El: level jm1 = level jm2) by (clear -l1 l2; lia).
  apply rmap_ext. now do 2 rewrite <-level_juice_level_phi; auto.
  intros l.
  specialize (rd1 l); specialize (rd2 l).
  rewrite level_juice_level_phi in *.
  destruct jm  as [m  phi  jmc  jmacc  jmma  jmall ].
  destruct jm1 as [m1 phi1 jmc1 jmacc1 jmma1 jmall1].
  destruct jm2 as [m2 phi2 jmc2 jmacc2 jmma2 jmall2].
  simpl in *.
  subst m2; rename m1 into m'.
  destruct rd1 as [jmno [E1 | [[sh1 [rsh1 [v1 [v1' [E1 E1']]]]] | [[pos1 [v1 E1]] | [v1 [pp1 [E1 E1']]]]]]];
  destruct rd2 as [_    [E2 | [[sh2 [rsh2 [v2 [v2' [E2 E2']]]]] | [[pos2 [v2 E2]] | [v2 [pp2 [E2 E2']]]]]]];
  try pose proof jmno pos1 as phino; try pose proof (jmno pos2) as phino; clear jmno;
    remember (phi  @ l) as x ;
    remember (phi1 @ l) as x1;
    remember (phi2 @ l) as x2;
    subst.

  - (* phi1: same   | phi2: same   *)
    congruence.

  - (* phi1: same   | phi2: update *)
    rewrite <- E1, El.
    rewrite El in E1.
    rewrite E1 in E2.
    destruct (jmc1 _ _ _ _ _ E2).
    destruct (jmc2 _ _ _ _ _ E2').
    congruence.

  - (* phi1: same   | phi2: alloc  *)
    exfalso.
    rewrite phino in E1. simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc2 l).
    rewrite E2 in jmacc2.
    simpl in jmacc2.
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: same   | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: update | phi2: same   *)
    rewrite <- E2, <-El.
    rewrite <-El in E2.
    rewrite E2 in E1.
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E1).
    congruence.

  - (* phi1: update | phi2: update *)
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E2').
    rewrite E1', E2'.
    destruct (phi@l); inv E1; inv E2.
    f_equal. apply proof_irr.
  - (* phi1: update | phi2: alloc  *)
    rewrite phino in E1.
    simpl in E1.
    inversion E1.

  - (* phi1: update | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence.  
  - (* phi1: alloc  | phi2: same   *)
    exfalso.
    rewrite phino in E2. simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc1 l).
    rewrite E1 in jmacc1.
    simpl in jmacc1.
    rewrite jmacc2 in jmacc1.
    clear -jmacc1.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial. 
  - (* phi1: alloc  | phi2: update *)
    rewrite phino in E2.
    simpl in E2.
    inversion E2.

  - (* phi1: alloc  | phi2: alloc  *)
    destruct (jmc1 _ _ _ _ _ E1).
    destruct (jmc2 _ _ _ _ _ E2).
    congruence.

  - (* phi1: alloc  | phi2: free   *)
    congruence.

  - (* phi2: free   | phi2: same   *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial.  
  - (* phi2: free   | phi2: update *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1 rsh2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence.
  - (* phi2: free   | phi2: alloc  *)
    congruence.

  - (* phi2: free   | phi2: free   *)
    congruence.
  - congruence.
Qed.
