Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.conclib.
Require Export iris.bi.lib.atomic.
Require Import VST.concurrency.invariants.
Require Import VST.concurrency.fupd.
Require Import VST.floyd.library.
Require Export VST.zlist.sublist.
Require Import Program.Equality.

Open Scope logic. (* we shouldn't need this *)

(* Thoughts on invariants and the two-level structure:
   I expect that our version of the operational semantics will keep nonatomic locations as is,
   so that the points-to assertions won't need view parameters (and in fact will be objective?).
   The question then is: do we need the two-level structure in which iGPS-style assertions are
   functions from view to mpred, or can even protocol assertions simply be mpreds? We might be able
   to use something like the external state construction to use ghost state to remember per-thread
   timestamps, so that we don't need to include timestamps in the rmap (or as an extra argument
   to assertions). In this model, there would be no objectivity requirement at all: instead,
   protocol assertions from other threads would be incompatible with the current thread because
   they refer to a different location for their timestamp ghost state.
   On the other hand, if we do need the two-level structure, we should still define invariants
   without objectivity here (as Iris-level invariants), and define iGPS-level invariants elsewhere. *)
(* We will still, of course, have to choose between SC and RA atomics in any given proof/program,
   since there's no soundness proof (or operational model) for a language with both. And invariants
   must still be accessible only via atomics. Does this make the fancy-update style useless,
   since we can't insert it into the definition of semax? Well, iGPS still uses it in the RA atomic
   rules, so maybe it's still useful. *)

Section atomics.

Context {inv_names : invG}.

Section atomicity.

(* The logical atomicity of Iris. *)

(* for people who don't want telescope notation *)
Definition tele_unwrap {A} (x : tele_arg (TeleS (fun _ : A => TeleO))) :=
  match x with
  | TargS _ _ x _ => x
  end.

Definition atomic_shift {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) : mpred :=
  @atomic_update mpredI _ [tele _ : A] [tele _ : B] Eo Ei (λ.. x, a (tele_unwrap x)) (λ.. x y, b (tele_unwrap x) (tele_unwrap y)) (λ.. x y, Q (tele_unwrap y)).

Lemma atomic_commit_fupd : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- (|==> (EX y, b x y * R' y))%I) ->
  (atomic_shift a Ei Eo b Q * R |-- |={Eo}=> (EX y, Q y * R' y))%I.
Proof.
  intros.
  iIntros "[AS R]".
  unfold atomic_shift.
  iMod "AS" as (x) "[a [_ commit]]"; simpl.
  iMod (H with "[$R $a]") as (y) "[b Q]".
  iExists y; iMod ("commit" with "b") as "$"; auto.
Qed.

Corollary atomic_commit_elim : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- (|==> (EX y, b x y * R' y))%I) ->
  (wsat * ghost_set g_en (coPset_to_Ensemble Eo) * atomic_shift a Ei Eo b Q * R |-- |==> ◇ (wsat * ghost_set g_en (coPset_to_Ensemble Eo) * (EX y, Q y * R' y)))%I.
Proof.
  intros.
  iIntros "[[[wsat en] AS] R]".
  iApply wsat_fupd_elim'; iFrame.
  iApply atomic_commit_fupd; eauto; iFrame.
Qed.

(* This is unsound: what we really need is fupd in WP.
   But that might not be necessary if we use atomic specs for all concurrent operations. *)
Lemma atomic_commit : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- (|==> (EX y, b x y * R' y))%I) ->
  (atomic_shift a Ei Eo b Q * R |-- |==> (EX y, Q y * R' y))%I.
Proof.
  intros.
  eapply atomic_commit_elim in H.
  admit.
Admitted.

Lemma atomic_rollback_fupd : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- (|==> a x * R')%I) ->
  (atomic_shift a Ei Eo b Q * R |-- |={Eo}=> atomic_shift a Ei Eo b Q * R')%I.
Proof.
  intros.
  iIntros "[AS R]".
  unfold atomic_shift.
  iMod "AS" as (x) "[a [rollback _]]"; simpl.
  iMod (H with "[$R $a]") as "[a R]".
  iMod ("rollback" with "a") as "$"; auto.
Qed.

Corollary atomic_rollback_elim : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- (|==> a x * R')%I) ->
  (wsat * ghost_set g_en (coPset_to_Ensemble Eo) * atomic_shift a Ei Eo b Q * R |-- |==> ◇ (wsat * ghost_set g_en (coPset_to_Ensemble Eo) * (atomic_shift a Ei Eo b Q * R')))%I.
Proof.
  intros.
  iIntros "[[[wsat en] AS] R]".
  iApply wsat_fupd_elim'; iFrame "wsat en".
  iApply atomic_rollback_fupd; eauto; iFrame.
Qed.

Lemma atomic_rollback : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- (|==> a x * R')%I) ->
  (atomic_shift a Ei Eo b Q * R |-- atomic_shift a Ei Eo b Q * R')%I.
Proof.
  intros.
  eapply atomic_rollback_elim in H.
  admit.
Admitted.

Lemma atomic_shift_mask_weaken {A B} Eo1 Eo2 Ei a (b : A -> B -> mpred) Q :
  Eo1 ⊆ Eo2 ->
  atomic_shift a Ei Eo1 b Q |-- atomic_shift a Ei Eo2 b Q.
Proof.
  intros; unfold atomic_shift.
  apply atomic_update_mask_weaken; auto.
Qed.

(* might be able to get rid of this if we do iInv instances *)
Lemma inv_atomic_shift : forall {A B} a Ei Eo (b : A -> B -> mpred) Q i R P
  (Hi : inv i ⊆ Eo) (Hio : Ei ⊆ Eo ∖ inv i)
  (Ha1 : (invariant i R * |>R |-- |={Eo ∖ inv i}=> EX x, a x * ((a x -* |={Ei}=> |>R) &&
    (ALL y, |> P * b x y -* |={Ei}=> |>R * Q y)))%I),
  invariant i R * |> P |-- atomic_shift a Ei Eo b Q.
Proof.
  intros; unfold atomic_shift.
  iIntros "[#I P]". iAuIntro.
  rewrite /atomic_acc /=.
  iMod (inv_open with "I") as "[R Hclose]"; first done.
  iMod (Ha1 with "[$I $R]") as (x) "(a & shift)".
  iExists x; iFrame "a".
  iMod fupd_mask_subseteq as "mask"; first done.
  iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("shift" with "a") as "R".
    iMod "mask"; iMod ("Hclose" with "R"); auto.
  - iIntros (y) "b".
    iMod ("shift" with "[$P $b]") as "[R Q]".
    iMod "mask"; iMod ("Hclose" with "R"); auto.
Qed.

Lemma atomic_shift_nonexpansive : forall {A B} n a Ei Eo (b : A -> B -> mpred) Q,
  approx n (atomic_shift a Ei Eo b Q) =
  approx n (atomic_shift (fun x => approx n (a x)) Ei Eo (fun x y => approx n (b x y)) (fun y => approx n (Q y))).
Proof.
  intros; unfold atomic_shift.
  destruct n as [|n].
  { rewrite !approx_0; auto. }
  unshelve eapply (atomic_update_ne _ _ n (λ.. x : [tele _ : A], a (tele_unwrap x))).
  { intros a1; simpl. dependent destruction a1; simpl.
    dependent destruction a1; simpl. hnf.
    rewrite approx_idem; auto. }
  { intros a1 b1; simpl.
    dependent destruction a1; simpl.
    dependent destruction a1; simpl.
    dependent destruction b1; simpl.
    dependent destruction b1; simpl.
    hnf. rewrite approx_idem; auto. }
  { intros a1 b1; simpl.
    dependent destruction a1; simpl.
    dependent destruction a1; simpl.
    dependent destruction b1; simpl.
    dependent destruction b1; simpl.
    hnf. rewrite approx_idem; auto. }
Qed.

Lemma atomic_shift_derives_frame : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred) R
  (Ha : (forall x, a x * |>R |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x * |>R) && ALL y' : _, b' x' y' -* |={Ei}=> EX y : _, b x y * (Q y -* |={Eo}=> Q' y')))%I),
  atomic_shift a Ei Eo b Q * |>R |-- atomic_shift a' Ei Eo b' Q'.
Proof.
  intros; unfold atomic_shift.
  iIntros "[AU P]". iAuIntro.
  iApply (aacc_aupd with "AU"); auto; simpl.
  iIntros (x) "a".
  iMod (Ha with "[$a $P]") as (x') "(a' & A)".
  rewrite /atomic_acc /=.
  iExists x'; iFrame "a'".
  iIntros "!>"; iSplit.
  - iIntros "a'".
    iMod ("A" with "a'") as "[$ $]"; auto.
  - iIntros (y') "b'".
    iMod ("A" with "b'") as (y) "[b HQ]".
    iRight; iExists y; iFrame; auto.
Qed.

Lemma atomic_shift_derives : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred)
  (Ha : (forall x, a x  |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x) && ALL y' : _, b' x' y' -* |={Ei}=> EX y : _, b x y * (Q y -* |={Eo}=> Q' y')))%I),
  atomic_shift a Ei Eo b Q |-- atomic_shift a' Ei Eo b' Q'.
Proof.
  intros; unfold atomic_shift.
  iIntros "AU". iAuIntro.
  iApply (aacc_aupd with "AU"); auto; simpl.
  iIntros (x) "a".
  iMod (Ha with "a") as (x') "[a' H']".
  iAaccIntro with "a'".
  - iIntros "a'". iMod ("H'" with "a'") as "$"; auto.
  - iIntros (y') "b'". iMod ("H'" with "b'") as (y) "[b H]".
    iRight; iExists y; iFrame; auto.
Qed.

Lemma atomic_shift_derives' : forall {A A' B} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B -> mpred) (Q : B -> mpred)
  (Ha : (forall x, a x |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x) && ALL y : _, b' x' y -* |={Ei}=> b x y))%I),
  atomic_shift a Ei Eo b Q |-- atomic_shift a' Ei Eo b' Q.
Proof.
  intros; apply atomic_shift_derives.
  iIntros (x) "a"; iMod (Ha with "a") as (x') "[a H]".
  iExists x'; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("H" with "a") as "$"; auto.
  - iIntros (y) "b"; iExists y.
    iDestruct "H" as "[_ H]".
    iMod ("H" with "b") as "$".
    iIntros "!> $"; auto.
Qed.

Lemma atomic_shift_derives_simple : forall {A B} (a a' : A -> mpred) Ei Eo (b b' : A -> B -> mpred) (Q : B -> mpred)
  (Ha1 : (forall x, a x |-- |={Ei}=> a' x)%I)
  (Ha2 : (forall x, a' x |-- |={Ei}=> a x)%I)
  (Hb : (forall x y, b' x y |-- |={Ei}=> b x y)%I),
  atomic_shift a Ei Eo b Q |-- atomic_shift a' Ei Eo b' Q.
Proof.
  intros; apply atomic_shift_derives'; intros.
  iIntros "a"; iExists x; iMod (Ha1 with "a") as "$".
  iIntros "!>"; iSplit.
  - iApply Ha2.
  - iIntros (?); iApply Hb.
Qed.

Lemma atomic_shift_exists : forall {A B} a Ei Eo (b : A -> B -> mpred) Q,
  atomic_shift (fun (_ : unit) => EX x : A, a x) Ei Eo (fun (_ : unit) => EX x : A, b x) Q |-- atomic_shift a Ei Eo b Q.
Proof.
  intros; unfold atomic_shift.
  iIntros "AU". iAuIntro.
  iApply (aacc_aupd with "AU"); auto; simpl.
  iIntros (_) "a"; iDestruct "a" as (x) "a".
  rewrite /atomic_acc /=.
  iExists x; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a !>".
    iSplitR ""; auto.
    iExists x; auto.
  - iIntros (y) "b !>".
    iRight; iExists y.
    iSplitR ""; auto.
    iExists x; auto.
Qed.

End atomicity.

End atomics.

Global Hint Resolve empty_subseteq : core.

Definition atomic_spec_type W T := ProdType (ProdType W (ArrowType (ConstType T) Mpred)) (ConstType invG).

Definition super_non_expansive_a {A W} (a : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A ts -> predicates_hered.pred rmap) :=
  forall n ts w x, approx n (a ts w x) =
  approx n (a ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x).

Definition super_non_expansive_b {A B W} (b : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A ts -> B ts -> predicates_hered.pred rmap) :=
  forall n ts w x y, approx n (b ts w x y) =
  approx n (b ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x y).

Definition super_non_expansive_la {W} la := @super_non_expansive_list W (fun ts w rho => map (fun l => !! (locald_denote l rho)) (la ts w)).

Definition super_non_expansive_lb {B W} lb := forall v : B, @super_non_expansive_list W (fun ts w rho => map (fun l => !! (locald_denote l rho)) (lb ts w v)).

Import List.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
(*Notation atomic_spec1 T W args tz la P a t lb b Ei Eo :=
  (mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) '(w, Q, inv_names) =>
     PROP ()
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
   (fun (ts: list Type) '(w, Q, inv_names) => EX v : T,
     PROP () (LOCALx (map (fun l => l ts w v) lb)
     (SEP (Q v)))) _ _).*)

Lemma atomic_spec_nonexpansive_pre' : forall {A T} {t : Inhabitant T} W P L G R S2 Ei Eo SQ
  (HP : @super_non_expansive_list W (fun ts a _ => map prop (P ts a)))
  (HL: forall n ts x, L ts x = L ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HG: @super_non_expansive_list W (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (HR : @super_non_expansive_list W (fun ts a _ => R ts a)),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @args_super_non_expansive (atomic_spec_type W T)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) =>
    let '(w, Q, inv_names) := _a in
    PROPx (P ts w) (PARAMSx (L ts w) (GLOBALSx (G ts w)
     (SEPx (atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q :: R ts w))))).
Proof.
  intros.
  hnf; intros.
  etransitivity; [|etransitivity; [
    apply (PROP_PARAMS_GLOBALS_SEP_args_super_non_expansive' (atomic_spec_type W T) (fun ts x => P ts (fst (fst x))) (fun ts x => L ts (fst (fst x))) (fun ts x => G ts (fst (fst x))) (fun ts '(w, Q, inv_names) => atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q :: R ts w))|]].
  - instantiate (9 := x). destruct x as ((?, ?), ?). reflexivity.
  - intros ? ? ((?, ?), ?) ?; apply HP; auto.
  - intros ? ? ((?, ?), ?); apply HL; auto.
  - intros ? ? ((?, ?), ?); apply HG; auto.
  - intros ? ? ((?, ?), ?) ?; constructor; [|apply HR; auto].
    rewrite -> atomic_shift_nonexpansive by auto; setoid_rewrite atomic_shift_nonexpansive at 2; auto.
    f_equal; f_equal; repeat extensionality; simpl.
    + apply H.
    + apply H0.
    + rewrite approx_idem; auto.
  - destruct x as ((?, ?), ?); reflexivity.
Qed.

Definition atomic_spec_type0 W := ProdType (ProdType W Mpred) (ConstType invG).

Lemma atomic_spec_nonexpansive_pre0 : forall {A} W P L G R S2 Ei Eo SQ
  (HP : super_non_expansive_list (fun ts w _ => map prop (P ts w)))
  (HL: forall n ts x, L ts x = L ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HG: @super_non_expansive_list W (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (HR : super_non_expansive_list (fun ts w _ => R ts w)),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @args_super_non_expansive (atomic_spec_type0 W)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) =>
    let '(w, Q, inv_names) := _a in
    PROPx (P ts w) (PARAMSx (L ts w) (GLOBALSx (G ts w)
     (SEPx (atomic_shift(A := A ts)(B := unit)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) (fun _ => Q) :: R ts w))))).
Proof.
  intros.
  hnf; intros.
  etransitivity; [|etransitivity; [
    apply (PROP_PARAMS_GLOBALS_SEP_args_super_non_expansive' (atomic_spec_type0 W) (fun ts x => P ts (fst (fst x))) (fun ts x => L ts (fst (fst x))) (fun ts x => G ts (fst (fst x))) (fun ts '(w, Q, inv_names) => atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) (fun _ => Q) :: R ts w))|]].
  - instantiate (9 := x). destruct x as ((?, ?), ?). reflexivity.
  - intros ? ? ((?, ?), ?) ?; apply HP; auto.
  - intros ? ? ((?, ?), ?); apply HL; auto.
  - intros ? ? ((?, ?), ?); apply HG; auto.
  - intros ? ? ((?, ?), ?) ?; constructor; [|apply HR; auto].
    rewrite -> atomic_shift_nonexpansive by auto; setoid_rewrite atomic_shift_nonexpansive at 2; auto.
    f_equal; f_equal; repeat extensionality; simpl.
    + apply H.
    + apply H0.
    + rewrite approx_idem; auto.
  - destruct x as ((?, ?), ?); reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_pre : forall {A T} {t : Inhabitant T} W P L G R S2 Ei Eo SQ Pre
  (Heq : (forall ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG),
   Pre ts _a = let '(w, Q, inv_names) := _a in
    PROPx (P ts w) (PARAMSx (L ts w) (GLOBALSx (G ts w)
     (SEPx (atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q :: R ts w))))))
  (HP : super_non_expansive_list (fun ts w _ => map prop (P ts w)))
  (HL: forall n ts x, L ts x = L ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HG: @super_non_expansive_list W (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (HR : super_non_expansive_list (fun ts w _ => R ts w)),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @args_super_non_expansive (atomic_spec_type W T) Pre.
Proof.
  intros.
  evar (Pre' : forall ts : list Type, functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG -> argsEnviron -> mpred).
  replace Pre with Pre'; subst Pre'; [apply (atomic_spec_nonexpansive_pre'(A := A)); eauto|].
  extensionality ts x; auto.
Qed.

Lemma atomic_spec_nonexpansive_post' : forall {T} W L R
  (HL : forall v, super_non_expansive_list (fun ts w rho => map (fun l => !! (locald_denote l rho)) (L ts w v)))
  (HR : forall v, super_non_expansive_list ((fun ts w _ => R ts w v))),
  @super_non_expansive (atomic_spec_type W T)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) =>
    let '(w, Q, inv_names) := _a in
    EX v : T,
    PROP () (LOCALx (L ts w v) (SEPx (Q v :: R ts w v)))).
Proof.
  intros.
  hnf; intros.
  destruct x as ((w, Q), inv_names).
  rewrite !approx_exp; f_equal; extensionality v.
  etransitivity; [|etransitivity; [
    apply (PROP_LOCAL_SEP_super_non_expansive' (atomic_spec_type W T) (fun ts '(w, _, _) => []) (fun ts '(w, _, _) => L ts w v) (fun ts '(w, Q, inv_names) => Q v :: R ts w v))|]].
  - instantiate (1 := rho); instantiate (1 := ts); instantiate (1 := (w, Q, inv_names)); reflexivity.
  - intros ? ? ((?, ?), ?) ?; constructor.
  - intros ? ? ((?, ?), ?) ?; apply HL; auto.
  - intros ? ? ((?, ?), ?) ?; constructor; [|apply HR; auto].
    simpl; rewrite approx_idem; auto.
  - reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_post0 : forall W L R
  (HL : super_non_expansive_list (fun ts w rho => map (fun l => !! (locald_denote l rho)) (L ts w)))
  (HR : super_non_expansive_list ((fun ts w _ => R ts w))),
  @super_non_expansive (atomic_spec_type0 W)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) =>
    let '(w, Q, inv_names) := _a in
    PROP () (LOCALx (L ts w) (SEPx (Q :: R ts w)))).
Proof.
  intros.
  hnf; intros.
  etransitivity; [|etransitivity; [
    apply (PROP_LOCAL_SEP_super_non_expansive' (atomic_spec_type0 W) (fun ts '(w, _, _) => []) (fun ts '(w, _, _) => L ts w) (fun ts '(w, Q, inv_names) => Q :: R ts w))|]].
  - instantiate (1 := rho); instantiate (1 := ts); instantiate (1 := x); destruct x as ((?, ?), ?); reflexivity.
  - intros ? ? ((?, ?), ?) ?; constructor.
  - intros ? ? ((?, ?), ?) ?; apply HL; auto.
  - intros ? ? ((?, ?), ?) ?; constructor; [|apply HR; auto].
    simpl; rewrite approx_idem; auto.
  - reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_post : forall {T} W L R Post
  (Heq : (forall ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG),
  Post ts _a = let '(w, Q, inv_names) := _a in
    EX v : T,
    PROP () (LOCALx (L ts w v) (SEPx (Q v :: R ts w v)))))
  (HL : forall v, super_non_expansive_list (fun ts w rho => map (fun l => !! (locald_denote l rho)) (L ts w v)))
  (HR : forall v, super_non_expansive_list ((fun ts w _ => R ts w v))),
  @super_non_expansive (atomic_spec_type W T) Post.
Proof.
  intros.
  evar (Post' : forall ts : list Type, functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG -> environ -> mpred).
  replace Post with Post'; subst Post'; [apply atomic_spec_nonexpansive_post'; eauto|].
  extensionality ts x; auto.
Qed.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec {A T} {t : Inhabitant T} W args tz la P G Qp a lb
        b Ei Eo
   (HP : super_non_expansive' P) (HQp : forall v:T, super_non_expansive' (Qp v))
  (Ha : super_non_expansive_a(A := A) a) (Hla: forall n ts x, la ts x = la ts (functors.MixVariantFunctor.fmap _ (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x))
  (HG: @super_non_expansive_list W (fun ts a rho => map (fun Q0 => prop (locald_denote (gvars Q0) rho)) (G ts a)))
  (Hlb : super_non_expansive_lb lb) (Hb : super_non_expansive_b b) :=
  mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
  (fun (ts: list Type) '(w, Q, inv_names) =>
    PROP ()
    (PARAMSx (la ts w) (GLOBALSx (G ts w) (
    (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))%assert5))))
  (fun (ts: list Type) '(w, Q, inv_names) => EX v : T,
    PROP () (LOCALx (lb ts w v)
    (SEP (Q v; Qp v ts w))%assert5)) _ _.
Next Obligation.
Proof.
  intros; eapply atomic_spec_nonexpansive_pre; try eassumption.
  { intros ? ((?, ?), ?). reflexivity. }
  all: auto.
  - constructor.
  - repeat constructor; repeat intro; auto.
Qed.
Next Obligation.
Proof.
  intros; eapply atomic_spec_nonexpansive_post.
  { intros ? ((?, ?), ?); reflexivity. }
  - auto.
  - repeat constructor.
    unfold super_non_expansive, super_non_expansive' in *.
    intros; apply HQp.
Qed.

Definition stable_spec_type W := ProdType (ProdType (ProdType W
  (ArrowType (DependentType 0) (ArrowType (DependentType 1) Mpred))) (ArrowType (DependentType 1) Mpred)) (ConstType invG).

(*Lemma stabilize : forall T W args tz P1 P2 Q1 Q2 neP1 neP2 neQ1 neQ2
  PP la P a lb b Ei Eo Q'
  (Hpre1 : forall ts w Q inv_names, P1 ts (w, Q, inv_names) =
     PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
  (Hpost1 : forall ts w Q inv_names, Q1 ts (w, Q, inv_names) =
     EX v : T, PROP () (LOCALx (map (fun l => l ts w v) lb) (SEP (Q v))))
  (Hpre2 : forall ts w b' Q inv_names, P2 ts (w, b', Q, inv_names) =
     PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; P ts w))))
  (Hpost2 : forall ts w b' Q inv_names, Q2 ts (w, b', Q, inv_names) =
    EX v1 : _, EX v2 : _,
     PROP () (LOCALx (map (fun l => l ts w v2) lb)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; Q' ts w v1 v2))))
  (Hb : forall ts w v1 v2, b ts w v1 v2 |-- a ts w v1 * Q' ts w v1 v2),
  funspec_sub (mk_funspec (pair args tz) cc_default (atomic_spec_type W T) P1 Q1 neP1 neQ1)
    (mk_funspec (pair args tz) cc_default (stable_spec_type W) P2 Q2 neP2 neQ2).
Proof.
  intros; apply subsume_subsume.
  unfold funspec_sub'; repeat (split; auto); intros.
  destruct x2 as (((w, b'), Q), inv_names).
  simpl funsig_of_funspec.
  rewrite Hpre2.
  set (AS := atomic_shift _ _ _ _ _).
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists ts2 (w, (fun v2 => AS * EX v1 : _, Q' ts2 w v1 v2), inv_names) emp.
  simpl in *; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    rewrite Hpre1.
    unfold PROPx, LOCALx, SEPx; simpl.
    do 2 (apply andp_derives; auto).
    unfold AS, atomic_shift; Intros P'; Exists P'; cancel.
    sep_apply cored_dup_cored.
    apply andp_derives; auto.
    iIntros "[H AS] P"; iMod ("H" with "P") as (v1) "[a H]".
    iExists v1; iFrame.
    iIntros "!>"; iSplit.
    + iIntros "a".
      iDestruct "AS" as "[_ e]"; iMod (cored_emp with "e") as "_".
      iApply "H"; auto.
    + iIntros (y) "b".
      iDestruct (Hb with "b") as "[a Q]".
      iMod ("H" with "a").
      iIntros "!>"; iSplitR "Q".
      * iExists P'; iFrame.
      * iExists v1; auto.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; auto.
    rewrite Hpost1 Hpost2.
    unfold PROPx, LOCALx, SEPx; simpl.
    eapply derives_trans, ghost_seplog.bupd_intro.
    Intros v2 v1; Exists v1 v2; rewrite sepcon_assoc; unfold AS; auto.
Qed.

Lemma stabilize0 : forall W args tz P1 P2 Q1 Q2 neP1 neP2 neQ1 neQ2
  PP la P a lb b Ei Eo Q'
  (Hpre1 : forall ts w Q inv_names, P1 ts (w, Q, inv_names) =
    PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(B := unit)(inv_names := inv_names) (a ts w) Ei Eo (b ts w) (fun _ => Q); P ts w))))
  (Hpost1 : forall ts w Q inv_names, Q1 ts (w, Q, inv_names) =
     PROP () (LOCALx (map (fun l => l ts w) lb) ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
  (Hpre2 : forall ts w b' Q inv_names, P2 ts (w, b', Q, inv_names) =
     PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; P ts w))))
  (Hpost2 : forall ts w b' Q inv_names, Q2 ts (w, b', Q, inv_names) =
    EX v1 : _,
     PROP () (LOCALx (map (fun l => l ts w) lb)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; Q' ts w v1))))
  (Hb : forall ts w v1, b ts w v1 tt |-- a ts w v1 * Q' ts w v1),
  funspec_sub (mk_funspec (pair args tz) cc_default (atomic_spec_type0 W) P1 Q1 neP1 neQ1)
    (mk_funspec (pair args tz) cc_default (stable_spec_type W) P2 Q2 neP2 neQ2).
Proof.
  intros; apply subsume_subsume.
  unfold funspec_sub'; repeat (split; auto); intros.
  destruct x2 as (((w, b'), Q), inv_names).
  simpl funsig_of_funspec.
  rewrite Hpre2.
  set (AS := atomic_shift _ _ _ _ _).
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists ts2 (w, (AS * EX v1 : _, Q' ts2 w v1), inv_names) emp.
  simpl in *; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    rewrite Hpre1.
    unfold PROPx, LOCALx, SEPx; simpl.
    do 2 (apply andp_derives; auto).
    unfold AS, atomic_shift; Intros P'; Exists P'; cancel.
    sep_apply cored_dup_cored.
    apply andp_derives; auto.
    iIntros "[H AS] P"; iMod ("H" with "P") as (v1) "[a H]".
    iExists v1; iFrame.
    iIntros "!>"; iSplit.
    + iIntros "a".
      iDestruct "AS" as "[_ e]"; iMod (cored_emp with "e") as "_".
      iApply "H"; auto.
    + iIntros ([]) "b".
      iDestruct (Hb with "b") as "[a Q]".
      iMod ("H" with "a").
      iIntros "!>"; iSplitR "Q".
      * iExists P'; iFrame.
      * iExists v1; auto.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; auto.
    rewrite Hpost1 Hpost2.
    unfold PROPx, LOCALx, SEPx; simpl.
    eapply derives_trans, ghost_seplog.bupd_intro.
    Intros v1; Exists v1; rewrite sepcon_assoc; unfold AS; auto.
Qed.*)

Require Import stdpp.hlist.

(* Adapted from personal correspondence with Jason Gross, this lets us manipulate tuple types like they were lists. *)
Fixpoint tuple_type (A : tlist) : Type :=
  match A with
  | tnil => unit
  | tcons A As => A * tuple_type As
  end.
Definition tcurry {A As B} (f : A -> tuple_type As -> B)
  : tuple_type (tcons A As) -> B
  := fun '(a, b) => f a b.

Fixpoint tuple_type_rev' (A : tlist) (acc : Type) : Type
  := match A with
     | tnil => acc
     | tcons A As => tuple_type_rev' As (acc * A)
     end.

Definition tuple_type_rev (A : tlist) : Type
  := match A with
     | tnil => unit
     | tcons A As => tuple_type_rev' As A
     end.

Fixpoint tcurry_rev' (A : tlist) (acc : Type) {struct A}
  : tuple_type_rev' A acc -> acc * tuple_type A
  := match A return tuple_type_rev' A acc -> acc * tuple_type A with
     | tnil => fun v => (v, tt)
     | tcons A As => fun v => let '(sf, a, v) := tcurry_rev' As _ v in
                              (sf, (a, v))
     end.
Definition tcurry_rev (A : tlist) : tuple_type_rev A -> tuple_type A
  := match A with
     | tnil => fun v => v
     | tcons A As => fun v => tcurry_rev' As A v
     end.

Definition rev_curry {A B} (f : tuple_type A -> B) : tuple_type_rev A -> B
  := fun v => f (tcurry_rev _ v).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x : A 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))))) ..)))
   (@atomic_spec_nonexpansive_pre' (fun _ => A) T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%logic .. (cons LQy%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%logic .. (cons LQy%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%logic .. (cons LQy%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons LQx%assert3 .. (cons LQy%assert3 nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert3 .. (cons SPy%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : (T -> mpred) => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
    @exp (environ -> mpred) _ T (fun r =>
     PROP () (LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))))) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post' W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) r => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons LQx%logic .. (cons LQy%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'PARAMS' () 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (PARAMSx nil (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Px%type .. (cons Py%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun _ : unit => S2) Ei Eo (fun _ _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) (_:unit) => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) _ _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, Ei at level 0, Eo at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 , .. , xn 'PRE'  [ u , .. , v ] 'PROP' () 'PARAMS' ( Lx ; .. ; Ly ) 'GLOBALS' ( Gx ; .. ; Gy ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%type .. (cons v%type nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROPx nil
     (PARAMSx (cons Lx%type .. (cons Ly%type nil) ..) (GLOBALSx (cons Gx .. (cons Gy nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..))))))))) ..)))
   (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn => tcurry (fun Q : mpred => tcurry (fun (inv_names : invG) (_ : tuple_type tnil) =>
     PROP () LOCAL () (SEPx (Q :: cons SPx .. (cons SPy nil) ..)))))) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Lx%type .. (cons Ly%type nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons Gx .. (cons Gy nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons S1x%logic .. (cons S1y%logic nil) ..))) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x => S2)) ..)))
      Ei Eo
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..))) ..)))
     _ _ _ _ _ _)
  (atomic_spec_nonexpansive_post0 W
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => nil)) ..)))
      (fun (ts: list Type) => rev_curry (tcurry (fun x1 => .. (tcurry (fun xn (_ : tuple_type tnil) => (cons SPx%assert5%assert3 .. (cons SPy%assert5%assert3 nil) ..))) ..))) _ _))
  (at level 200, x1 closed binder, xn closed binder, x at level 0, Ei at level 0, Eo at level 0, S2 at level 0).

Ltac atomic_nonexpansive_tac := try (let x := fresh "x" in intros ?? x;
  try match type of x with list Type => (let ts := fresh "ts" in rename x into ts; intros x) end;
  repeat destruct x as [x ?]; unfold rev_curry, tcurry; simpl; auto); repeat constructor.

Global Obligation Tactic := atomic_nonexpansive_tac.

(* change start_function to handle curried arguments -- also thanks to Jason *)
Ltac read_names term :=
  lazymatch term with
  | tcurry (fun x : ?T => ?f)
    => let f' := fresh in
       let rest := lazymatch
             constr:(
               fun x : T
               => match f return _ with
                  | f' => ltac:(let f := (eval cbv delta [f'] in f') in
                                clear f';
                                let rest := read_names f in
                                refine rest)
                  end) with
           | fun _ => ?rest => rest
           | ?e => fail 0 "Could not eliminate the functional dependencies of" e
           end in
       constr:(((fun x : unit => x), rest))
  | _ => constr:(tt)
  end.

Ltac destruct_args t i :=
  match t with
  | tt => idtac
  | (fun x => _, ?t') => destruct_args t' i; (destruct i as [i x] || rename i into x)
  end.

Ltac start_function1 ::=
 leaf_function;
 lazymatch goal with |- semax_body ?V ?G ?F ?spec =>
    check_normalized F;
    function_body_unsupported_features F;
    let s := fresh "spec" in
    pose (s:=spec); hnf in s; cbn zeta in s; (* dependent specs defined with Program Definition often have extra lets *)
   repeat lazymatch goal with
    | s := (_, NDmk_funspec _ _ _ _ _) |- _ => fail
    | s := (_, mk_funspec _ _ _ _ _ _ _) |- _ => fail
    | s := (_, ?a _ _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _) |- _ => unfold a in s
    | s := (_, ?a _) |- _ => unfold a in s
    | s := (_, ?a) |- _ => unfold a in s
    end;
    lazymatch goal with
    | s :=  (_,  WITH _: globals
               PRE  [] main_pre _ _ _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s;
   unfold NDmk_funspec'
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 unfold NDmk_funspec;
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>

   split3; [check_parameter_types' | check_return_type | ];
    match Pre with
   | (fun _ => rev_curry ?t) => let i := fresh in let x := read_names t in intros Espec DependedTypeList i; destruct_args x i; unfold rev_curry, tcurry; simpl tcurry_rev; cbn match (* added line *)
   | (fun _ => convertPre _ _ (fun i => _)) =>  intros Espec DependedTypeList i
   | (fun _ x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun _ i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 try match goal with |- semax _ (fun rho => ?A rho * ?B rho)%logic _ _ =>
     change (fun rho => ?A rho * ?B rho)%logic with (A * B)%logic
  end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 rewrite_old_main_pre;
 repeat match goal with
 | |- @semax _ _ _ (match ?p with (a,b) => _ end * _)%logic _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _)%logic _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
             destruct p as [a b]
 | |- semax _ (close_precondition _
                                                (fun ae => !! (Datatypes.length (snd ae) = ?A) && ?B
                                                      (make_args ?C (snd ae) (mkEnviron (fst ae) _ _))) * _)%logic _ _ =>
          match B with match ?p with (a,b) => _ end => destruct p as [a b] end
       end;
(* this speeds things up, but only in the very rare case where it applies,
   so maybe not worth it ...
  repeat match goal with H: reptype _ |- _ => progress hnf in H; simpl in H; idtac "reduced a reptype" end;
*)
 try start_func_convert_precondition.

(* can we not do this? *)
Ltac start_function2 ::=
  first [ setoid_rewrite (* changed from erewrite *) compute_close_precondition_eq; [ | reflexivity | reflexivity]
        | rewrite close_precondition_main ].
