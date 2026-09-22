Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Overloading.LangD.Maps.
Require Import Overloading.LangD.Definitions.
Require Import Overloading.LangD.Typing.
Require Import Stdlib.Relations.Relation_Operators.
Open Scope string_scope.

Lemma canonical_form_arrow_m :
  forall em t1 t2,
    has_type_m [] em (Ty_Arrow t1 t2) ->
    value_m em ->
    exists x body,
      em = EM_Abs x t1 body.
Proof.
  intros.
  inversion H; subst; inversion H0.
  exists x, e.
  reflexivity.
Qed.

Lemma canonical_form_nat_m :
  forall em,
    has_type_m [] em Ty_Nat ->
    value_m em ->
    exists n,
      em = EM_Const n.
Proof.
  intros.
  inversion H; subst; inversion H0.
  exists n.
  reflexivity.
Qed.

Lemma canonical_form_bool_m :
  forall em,
    has_type_m [] em Ty_Bool ->
    value_m em ->
    em = EM_Bool true \/ em = EM_Bool false.
Proof.
  intros.
  inversion H; subst; inversion H0.
  destruct b; [left | right]; reflexivity.
Qed.

Lemma canonical_form_tuple_m :
  forall em t1 t2,
    has_type_m [] em (Ty_Tuple t1 t2) ->
    value_m em ->
    exists v1 v2,
      em = EM_Pair v1 v2 /\ value_m v1 /\ value_m v2.
Proof.
  intros.
  inversion H; subst; inversion H0.
  exists e1, e2.
  repeat split; try assumption.
Qed.

Definition includedin_m (Gamma Gamma' : context_m) : Prop :=
  forall x sch, var_lookup_m Gamma x sch -> var_lookup_m Gamma' x sch.

Lemma includedin_m_update : forall Gamma Gamma' x sch,
  includedin_m Gamma Gamma' ->
  includedin_m ((x, sch) :: Gamma) ((x, sch) :: Gamma').
Proof.
  intros. unfold includedin_m in *. intros.
  destruct (String.eqb_spec x x0).
  - subst.
    inversion H0; subst.
    + constructor.
    + constructor.
      * assumption.
      * apply H. assumption.
  - apply VLM_There.
    + symmetry. assumption.
    + apply H. inversion H0; subst.
      * contradiction n. reflexivity.
      * assumption.
Qed.

Lemma var_lookup_m_weakening : forall Gamma Gamma' x sch,
  var_lookup_m Gamma x sch ->
  var_lookup_m (List.app Gamma Gamma') x sch.
Proof.
  intros Gamma Gamma' x sch H.
  induction H; simpl.
  - apply VLM_Here.
  - apply VLM_There; assumption.
Qed.

Lemma weakening_m :
  forall Gamma Gamma' e tau,
    has_type_m Gamma e tau ->
    has_type_m (List.app Gamma Gamma') e tau.
Proof.
  intros. generalize dependent Gamma'. induction H; intros; simpl.
  - constructor.
  - constructor.
  - constructor.
  - apply TM_Var with (sch := sch).
    + apply var_lookup_m_weakening. assumption.
    + assumption.
  - apply TM_App with (t1 := t1).
    + apply IHhas_type_m1.
    + apply IHhas_type_m2.
  - apply TM_Add.
    + apply IHhas_type_m1.
    + apply IHhas_type_m2.
  - apply TM_Abs. apply IHhas_type_m.
  - apply TM_Let with (t1 := t1).
    + intros ts_args Tinst Hinst.
      apply H0 with (ts_args := ts_args); assumption.
    + apply IHhas_type_m.
  - apply TM_If.
    + apply IHhas_type_m1.
    + apply IHhas_type_m2.
    + apply IHhas_type_m3.
  - apply TM_Pair.
    + apply IHhas_type_m1.
    + apply IHhas_type_m2.
  - apply TM_Fst with (t2 := t2).
    + apply IHhas_type_m.
  - apply TM_Snd with (t1 := t1).
    + apply IHhas_type_m.
Qed.

Lemma weakening_empty_m :
  forall Gamma em t,
    has_type_m [] em t ->
    has_type_m Gamma em t.
Proof.
  intros.
  apply weakening_m with (Gamma' := Gamma) in H.
  simpl in *. assumption.
Qed.

Lemma var_lookup_m_shadow : forall x sch1 sch2 Gamma z tz,
  var_lookup_m ((x, sch1) :: (x, sch2) :: Gamma) z tz ->
  var_lookup_m ((x, sch1) :: Gamma) z tz.
Proof.
  intros x sch1 sch2 Gamma z tz H.
  inversion H; subst.
  - constructor.
  - inversion H6; subst.
    + contradiction.
    + apply VLM_There; assumption.
Qed.

Lemma var_lookup_m_shadow_prefix : forall prefix x sch1 sch2 Gamma z tz,
  var_lookup_m (prefix ++ (x, sch1) :: (x, sch2) :: Gamma)%list z tz ->
  var_lookup_m (prefix ++ (x, sch1) :: Gamma)%list z tz.
Proof.
  induction prefix; intros x sch1 sch2 Gamma z tz Hlook; simpl in *.
  - apply var_lookup_m_shadow with (sch2 := sch2). assumption.
  - destruct a as [y ty]. inversion Hlook; subst.
    + constructor.
    + apply VLM_There; [assumption |].
      apply IHprefix with (sch2 := sch2). assumption.
Qed.

Lemma has_type_m_shadow_prefix : forall prefix Gamma e T x sch1 sch2,
  has_type_m (prefix ++ (x, sch1) :: (x, sch2) :: Gamma)%list e T ->
  has_type_m (prefix ++ (x, sch1) :: Gamma)%list e T.
Proof.
  intros prefix Gamma e T x sch1 sch2 Htyp.
  remember (prefix ++ (x, sch1) :: (x, sch2) :: Gamma)%list as Gamma0.
  generalize dependent prefix.
  generalize dependent Gamma.
  generalize dependent sch2.
  generalize dependent sch1.
  generalize dependent x.
  induction Htyp; intros x0 sch1' sch2' Gamma' prefix' Heq; subst.
  - constructor.
  - constructor.
  - constructor.
  - apply TM_Var with (sch := sch).
    + eapply var_lookup_m_shadow_prefix. exact H.
    + assumption.
  - eapply TM_App; [eapply IHHtyp1; reflexivity | eapply IHHtyp2; reflexivity].
  - apply TM_Add; [eapply IHHtyp1; reflexivity | eapply IHHtyp2; reflexivity].
  - apply TM_Abs. eapply IHHtyp with (prefix := (x, Ty_Forall [] t1) :: prefix'). reflexivity.
  - eapply TM_Let.
    + intros ts_args Tinst Hinst.
      eapply (H0 ts_args Tinst Hinst) with (prefix := prefix'). reflexivity.
    + simpl. eapply IHHtyp with (prefix := (x, Ty_Forall ts t1) :: prefix'). reflexivity.
  - eapply TM_If; [eapply IHHtyp1; reflexivity | eapply IHHtyp2; reflexivity | eapply IHHtyp3; reflexivity].
  - apply TM_Pair; [eapply IHHtyp1; reflexivity | eapply IHHtyp2; reflexivity].
  - eapply TM_Fst. eapply IHHtyp. reflexivity.
  - eapply TM_Snd. eapply IHHtyp. reflexivity.
Qed.

Lemma has_type_m_shadow : forall x sch1 sch2 Gamma e t,
  has_type_m ((x, sch1) :: (x, sch2) :: Gamma) e t ->
  has_type_m ((x, sch1) :: Gamma) e t.
Proof.
  intros.
  apply (has_type_m_shadow_prefix [] Gamma e t x sch1 sch2).
  exact H.
Qed.

Lemma var_lookup_m_permute : forall x1 x2 sch1 sch2 Gamma z tz,
  x1 <> x2 ->
  var_lookup_m ((x1, sch1) :: (x2, sch2) :: Gamma) z tz ->
  var_lookup_m ((x2, sch2) :: (x1, sch1) :: Gamma) z tz.
Proof.
  intros x1 x2 sch1 sch2 Gamma z tz Hneq Hlook.
  inversion Hlook; subst.
  - apply VLM_There.
    + intros Heq; subst. apply Hneq. reflexivity.
    + constructor.
  - inversion H5; subst.
    + constructor.
    + apply VLM_There; [assumption |].
      apply VLM_There; assumption.
Qed.

Lemma var_lookup_m_permute_prefix : forall prefix x1 x2 sch1 sch2 Gamma z tz,
  x1 <> x2 ->
  var_lookup_m (prefix ++ (x1, sch1) :: (x2, sch2) :: Gamma)%list z tz ->
  var_lookup_m (prefix ++ (x2, sch2) :: (x1, sch1) :: Gamma)%list z tz.
Proof.
  induction prefix; intros x1 x2 sch1 sch2 Gamma z tz Hneq Hlook; simpl in *.
  - apply var_lookup_m_permute; assumption.
  - destruct a as [y ty]. inversion Hlook; subst.
    + constructor.
    + apply VLM_There; [assumption |].
      apply IHprefix; assumption.
Qed.

Lemma has_type_m_permute_prefix : forall prefix Gamma e T x1 x2 sch1 sch2,
  x1 <> x2 ->
  has_type_m (prefix ++ (x1, sch1) :: (x2, sch2) :: Gamma)%list e T ->
  has_type_m (prefix ++ (x2, sch2) :: (x1, sch1) :: Gamma)%list e T.
Proof.
  intros prefix Gamma e T x1 x2 sch1 sch2 Hneq Htyp.
  remember (prefix ++ (x1, sch1) :: (x2, sch2) :: Gamma)%list as Gamma0.
  generalize dependent prefix.
  generalize dependent Gamma.
  generalize dependent sch2.
  generalize dependent sch1.
  generalize dependent x1.
  generalize dependent x2.
  induction Htyp; intros x2 x1 Hneq sch1' sch2' Gamma' prefix' Heq; subst.
  - constructor.
  - constructor.
  - constructor.
  - apply TM_Var with (sch := sch).
    + eapply var_lookup_m_permute_prefix; eassumption.
    + assumption.
  - eapply TM_App.
    + eapply IHHtyp1; [assumption | reflexivity].
    + eapply IHHtyp2; [assumption | reflexivity].
  - apply TM_Add; [eapply IHHtyp1; [assumption | reflexivity] | eapply IHHtyp2; [assumption | reflexivity]].
  - apply TM_Abs.
    apply IHHtyp with (prefix := (x, Ty_Forall [] t1) :: prefix'); [assumption | reflexivity].
  - eapply TM_Let.
    + intros ts_args Tinst Hinst.
      eapply (H0 ts_args Tinst Hinst) with (prefix := prefix'); [assumption | reflexivity].
    + eapply IHHtyp with (prefix := (x, Ty_Forall ts t1) :: prefix'); [assumption | reflexivity].
  - eapply TM_If.
    + eapply IHHtyp1; [assumption | reflexivity].
    + apply IHHtyp2; [assumption | reflexivity].
    + apply IHHtyp3; [assumption | reflexivity].
  - apply TM_Pair; [eapply IHHtyp1; [assumption | reflexivity] | eapply IHHtyp2; [assumption | reflexivity]].
  - eapply TM_Fst. eapply IHHtyp; [assumption | reflexivity].
  - eapply TM_Snd. eapply IHHtyp; [assumption | reflexivity].
Qed.

Lemma has_type_m_permute : forall x1 x2 sch1 sch2 Gamma e t,
  x1 <> x2 ->
  has_type_m ((x1, sch1) :: (x2, sch2) :: Gamma) e t ->
  has_type_m ((x2, sch2) :: (x1, sch1) :: Gamma) e t.
Proof.
  intros.
  apply (has_type_m_permute_prefix [] Gamma e t x1 x2 sch1 sch2); assumption.
Qed.

Lemma substitution_preserves_typing_m :
  forall Gamma x sch v e T,
    has_type_m ((x, sch) :: Gamma) e T ->
    (forall ts Tinst, instantiate sch ts Tinst -> has_type_m [] v Tinst) ->
    has_type_m Gamma (subst_m x v e) T.
Proof.
  intros Gamma x sch v e T Htyp_e Htyp_v.
  generalize dependent Gamma.
  generalize dependent T.
  generalize dependent sch.
  induction e; intros sch Htyp_v T Gamma Htyp_e; simpl.
  - inversion Htyp_e; subst; constructor.
  - inversion Htyp_e; subst; constructor.
  - inversion Htyp_e; subst; constructor.
  -
    destruct (String.eqb_spec x x0); subst.
    + inversion Htyp_e as [ | | | ? ? ? ? ? Hlook Hinst | | | | | | | | ]; subst.
      inversion Hlook; subst.
      * apply Htyp_v in Hinst. apply weakening_empty_m. assumption.
      * contradiction.
    + inversion Htyp_e as [ | | | ? ? ? ? ? Hlook Hinst | | | | | | | | ]; subst.
      eapply TM_Var.
      * inversion Hlook; subst.
        -- contradiction n. reflexivity.
        -- eassumption.
      * exact Hinst.
  -
    inversion Htyp_e; subst.
    eapply TM_App; [ eapply IHe1 | eapply IHe2 ]; eassumption.
  -
    inversion Htyp_e; subst.
    apply TM_Add; [ eapply IHe1 | eapply IHe2 ]; eassumption.
  -
    inversion Htyp_e; subst.
    apply TM_Abs.
    destruct (String.eqb_spec x x0); subst.
    + eapply has_type_m_shadow; eassumption.
    + eapply IHe; [ eassumption | ].
      apply has_type_m_permute; [ symmetry; assumption | assumption ].
  -
    inversion Htyp_e; subst.
    eapply TM_Let.
    + intros ts_args Tinst Hinst.
      eapply IHe1; [ eassumption | eauto ].
    + destruct (String.eqb_spec x x0); subst.
      * eapply has_type_m_shadow; eassumption.
      * eapply IHe2; [ eassumption | ].
        apply has_type_m_permute; [ symmetry; assumption | assumption ].
  -
    inversion Htyp_e; subst.
    apply TM_Pair; [ eapply IHe1 | eapply IHe2 ]; eassumption.
  -
    inversion Htyp_e; subst.
    eapply TM_Fst; eapply IHe; eassumption.
  -
    inversion Htyp_e; subst.
    eapply TM_Snd; eapply IHe; eassumption.
  -
    inversion Htyp_e; subst.
    apply TM_If; [ eapply IHe1 | eapply IHe2 | eapply IHe3 ]; eassumption.
Qed.

Theorem progress_m :
  forall em t,
    has_type_m [] em t ->
    value_m em \/ (exists em', step_m em em').
Proof.
  intros.
  remember [] as Gamma. induction H; subst; eauto.
  - inversion H.
  -
    destruct (IHhas_type_m1 eq_refl); destruct (IHhas_type_m2 eq_refl); eauto.
    +
      apply canonical_form_arrow_m in H; try assumption.
      destruct H as [x [body Heq]]; subst.
      right. exists (subst_m x e2 body). constructor.
      assumption.
    +
      right. destruct H2 as [em' Hstep]. exists (EM_App e1 em').
      constructor. assumption. assumption.
    +
      right. destruct H1 as [em' Hstep]. exists (EM_App em' e2).
      constructor. assumption.
    +
      right. destruct H1 as [em1 Hstep1]. destruct H2 as [em2 Hstep2].
      exists (EM_App em1 e2).
      constructor. assumption.
  -
    destruct (IHhas_type_m1 eq_refl); destruct (IHhas_type_m2 eq_refl); eauto.
    +
      apply canonical_form_nat_m in H; try assumption.
      destruct H as [n1 Heq1]; subst.
      apply canonical_form_nat_m in H0; try assumption.
      destruct H0 as [n2 Heq2]; subst.
      right. exists (EM_Const (n1 + n2)). constructor.
    +
      right. destruct H2 as [em' Hstep]. exists (EM_Add e1 em').
      constructor. assumption. assumption.
    +
      right. destruct H1 as [em' Hstep]. exists (EM_Add em' e2).
      constructor. assumption.
    +
      right. destruct H1 as [em1 Hstep1]. destruct H2 as [em2 Hstep2].
      exists (EM_Add em1 e2).
      constructor. assumption.
  -
    right.
    destruct (scheme_has_instance ts t1) as [Tinst Hinst].
    destruct (H0 (repeat Ty_Nat (List.length ts)) Tinst Hinst eq_refl) as [Hval1 | [e1' Hstep1]].
    + exists (subst_m x e1 e2). constructor. assumption.
    + exists (EM_Let x ts e1' e2). constructor. assumption.
  -
    destruct (IHhas_type_m1 eq_refl); eauto.
    + apply canonical_form_bool_m in H; try assumption.
      destruct H; subst; right.
      * exists e2. constructor.
      * exists e3. constructor.
    + destruct H2. right.
      exists (EM_If x e2 e3). constructor. assumption.
  -
    destruct (IHhas_type_m1 eq_refl); destruct (IHhas_type_m2 eq_refl); eauto.
    +
      right. destruct H2. exists (EM_Pair e1 x). constructor. assumption.
      assumption.
    +
      right. destruct H1.
      exists (EM_Pair x e2).
      constructor. assumption.
    +
      right. destruct H1 as [em' Hstep]. exists (EM_Pair em' e2).
      constructor. assumption.
  -
    destruct (IHhas_type_m eq_refl); eauto.
    + apply canonical_form_tuple_m in H; try assumption.
      destruct H as [v1 [v2 [Heq [Hv1 Hv2]]]]; subst.
      right. exists v1. constructor. assumption.
      assumption.
    + destruct H0. right. exists (EM_Fst x). constructor. assumption.
  -
    destruct (IHhas_type_m eq_refl); eauto.
    + apply canonical_form_tuple_m in H; try assumption.
      destruct H as [v1 [v2 [Heq [Hv1 Hv2]]]]; subst.
      right. exists v2. constructor. assumption.
      assumption.
    + destruct H0. right. exists (EM_Snd x). constructor. assumption.
Qed.

Theorem preservation_m :
  forall em em' t,
    has_type_m [] em t ->
    step_m em em' ->
    has_type_m [] em' t.
Proof.
  intros em em' t Htyp_em Hstep_em.
  generalize dependent t.
  induction Hstep_em; intros; inversion Htyp_em; subst.
  -
    inversion H3; subst.
    apply substitution_preserves_typing_m with (sch := Ty_Forall [] t1); try assumption.
    intros ts Tinst Hinst.
    apply instantiate_nil in Hinst. destruct Hinst; subst.
    assumption.
  -
    eapply TM_App; [ apply IHHstep_em; eassumption | eassumption ].
  -
    eapply TM_App; [ eassumption | apply IHHstep_em; eassumption ].
  -
    constructor.
  -
    apply TM_Add; [ apply IHHstep_em; eassumption | assumption ].
  -
    apply TM_Add; [ assumption | apply IHHstep_em; eassumption ].
  -
    eapply TM_Let.
    + intros ts_args Tinst Hinst.
      apply IHHstep_em.
      eauto.
    + eassumption.
  -
    apply substitution_preserves_typing_m with (sch := Ty_Forall ts t1); try eassumption.
  -
    assumption.
  -
    assumption.
  -
    apply TM_If; [ apply IHHstep_em; eassumption | assumption | assumption ].
  -
    apply TM_Pair; [ apply IHHstep_em; eassumption | assumption ].
  -
    apply TM_Pair; [ assumption | apply IHHstep_em; eassumption ].
  -
    inversion H3; subst. assumption.
  -
    eapply TM_Fst; apply IHHstep_em; eassumption.
  -
    inversion H3; subst. assumption.
  -
    eapply TM_Snd; apply IHHstep_em; eassumption.
Qed.

Definition stuck_m (t: expr_m) : Prop :=
  (normal_form step_m) t /\ not (value_m t).

Definition multistep_m := multi step_m.

Theorem soundness_m :
  forall em em' t,
    has_type_m [] em t ->
    multistep_m em em' ->
    not (stuck_m em').
Proof.
  intros em em' t Htyp_em Hmulti_em.
  induction Hmulti_em; intros Hstuck.
  -
    unfold stuck_m in Hstuck. destruct Hstuck as [Hnormal Hnotvalue].
    apply progress_m in Htyp_em. destruct Htyp_em as [Hvalue | [em'' Hstep]].
    + contradiction.
    + unfold normal_form in Hnormal. apply Hnormal.
      exists em''. assumption.
  -
    unfold stuck_m in Hstuck. destruct Hstuck as [Hnormal Hnotvalue].
    apply preservation_m with (em := x) (em' := y) (t := t) in Htyp_em; try assumption.
    apply IHHmulti_em; try assumption.
    unfold normal_form.
    split. assumption.
    assumption.
Qed.

Lemma mono_preserves_value :
  forall Omega v vm,
    value v ->
    mono_expr Omega v vm ->
    value_m vm.
Proof.
  intros. induction H0; try (inversion H; subst; eauto).
Qed.

Lemma context_matches_lookup :
  forall Gamma Gamma_m x sch,
    context_matches Gamma Gamma_m ->
    variable_lookup Gamma x sch ->
    var_lookup_m Gamma_m x sch.
Proof.
  intros Gamma Gamma_m x sch Hmatch.
  induction Hmatch; intros Hlook; inversion Hlook; subst; eauto.
Qed.

Lemma instance_env_matches_update :
  forall Delta Omega n tvs t,
    instance_env_matches Delta Omega ->
    (forall ts Tinst em,
      instantiate (Ty_Forall tvs t) ts Tinst ->
      In (n, ts, em) Omega ->
      has_type_m [] em Tinst) ->
    instance_env_matches (update_properties Delta n (Ty_Forall tvs t)) Omega.
Proof.
  intros. unfold instance_env_matches in *. intros.
  destruct (String.eqb_spec n n0).
  - subst.
    unfold property_lookup, update_properties in H1.
    rewrite update_eq in H1. inversion H1; subst.
    eapply H0; eassumption.
  - eapply H.
    unfold property_lookup, update_properties in H1.
    rewrite update_neq in H1; try assumption.
    exact H1.
    symmetry. assumption.
    eassumption.
    assumption.
Qed.

Theorem monomorphization_preserves_typing :
  forall Gamma Delta e t,
    has_type Gamma Delta e t ->
    forall Omega em Gamma_m,
      instance_env_matches Delta Omega ->
      context_matches Gamma Gamma_m ->
      mono_expr Omega e em ->
      (forall n tvs t0 ts Tinst em0,
        instantiate (Ty_Forall tvs t0) ts Tinst ->
        In (n, ts, em0) Omega ->
        has_type_m [] em0 Tinst) ->
      has_type_m Gamma_m em t.
Proof.
  intros Gamma Delta e t Htyp.
  induction Htyp; intros Omega em Gamma_m Hmatch_env Hmatch_ctx Hmono Hinst_valid.
  -
    inversion Hmono; subst.
    constructor.
  -
    inversion Hmono; subst.
    constructor.
  -
    inversion Hmono; subst.
    constructor.
  -
    inversion Hmono; subst.
    eapply TM_Var.
    + eapply context_matches_lookup; eassumption.
    + assumption.
  -
    inversion Hmono; subst.
    apply weakening_empty_m.
    eapply Hmatch_env; eassumption.
  -
    inversion Hmono; subst.
    eapply TM_App.
    + eapply IHHtyp1; eassumption.
    + eapply IHHtyp2; eassumption.
  -
    inversion Hmono; subst.
    eapply TM_Add.
    + eapply IHHtyp1; eassumption.
    + eapply IHHtyp2; eassumption.
  -
    inversion Hmono; subst.
    eapply IHHtyp.
    + apply instance_env_matches_update.
      * exact Hmatch_env.
      * intros ts0 Tinst0 em0 Hinst Hin.
        eapply Hinst_valid; eassumption.
    + exact Hmatch_ctx.
    + eassumption.
    + exact Hinst_valid.
  -
    inversion Hmono; subst.
    constructor.
    eapply IHHtyp.
    + exact Hmatch_env.
    + constructor. exact Hmatch_ctx.
    + eassumption.
    + exact Hinst_valid.
  -
    inversion Hmono; subst.
    eapply TM_Let.
    + intros ts_args Tinst Hinst.
      eapply (H0 ts_args Tinst Hinst); eassumption.
    + eapply IHHtyp.
      * exact Hmatch_env.
      * constructor. exact Hmatch_ctx.
      * eassumption.
      * exact Hinst_valid.
  -
    inversion Hmono; subst.
    constructor.
    + eapply IHHtyp1; eassumption.
    + eapply IHHtyp2; eassumption.
    + eapply IHHtyp3; eassumption.
  -
    inversion Hmono; subst.
    eapply TM_Pair.
    + eapply IHHtyp1; eassumption.
    + eapply IHHtyp2; eassumption.
  -
    inversion Hmono; subst.
    eapply TM_Fst.
    eapply IHHtyp; eassumption.
  -
    inversion Hmono; subst.
    eapply TM_Snd.
    eapply IHHtyp; eassumption.
Qed.

Corollary monomorphization_soundness_with_selection :
  forall Gamma Delta e t Omega em Gamma_m catalog,
    has_type Gamma Delta e t ->
    valid_monomorphization catalog Omega ->
    instance_env_matches Delta Omega ->
    context_matches Gamma Gamma_m ->
    mono_expr Omega e em ->
    (forall n tvs t0 ts Tinst em0,
      instantiate (Ty_Forall tvs t0) ts Tinst ->
      In (n, ts, em0) Omega ->
      has_type_m [] em0 Tinst) ->
    has_type_m Gamma_m em t.
Proof.
  intros.
  eapply monomorphization_preserves_typing; eassumption.
Qed.

Lemma not_in_app_or : forall (A : Type) (l1 l2 : list A) (x : A),
  ~ In x (l1 ++ l2) <-> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A l1 l2 x. split; intros H.
  - split; intros H1; apply H; apply in_or_app; [left | right]; assumption.
  - destruct H as [H1 H2]. intros H3. apply in_app_or in H3. destruct H3; [apply H1 | apply H2]; assumption.
Qed.

Definition closed_instance_env (Omega : instance_env) : Prop :=
  forall n ts em,
    In (n, ts, em) Omega ->
    free em = [].

Lemma in_in_remove : forall A eq_dec (l : list A) (x y : A),
  x <> y -> In x l -> In x (remove eq_dec y l).
Proof.
  intros.
  induction l; simpl in *.
  - assumption.
  - destruct (eq_dec a y).
    + subst. destruct H0.
      * symmetry in H0. contradiction.
      * destruct (eq_dec y y).
        -- apply IHl. assumption.
        -- contradiction.
    + destruct H0.
      * subst. destruct (eq_dec y x).
        -- symmetry in e. contradiction.
        -- simpl. left. reflexivity.
      * subst. destruct (eq_dec y a).
        -- subst. apply IHl. assumption.
        -- simpl. right. apply IHl. assumption.
Qed.

Lemma not_in_remove : forall A eq_dec (l : list A) (x y : A),
  x <> y -> ~ In x l -> ~ In x (remove eq_dec y l).
Proof.
  intros. intros H1.
  apply in_remove in H1.
  destruct H1 as [Hin _].
  contradiction.
Qed.

Lemma subst_not_free_m : forall e x v,
  ~ In x (free e) ->
  subst_m x v e = e.
Proof.
  intros.
  induction e; simpl; try reflexivity.
  -
    destruct (String.eqb_spec x x0); subst.
    + simpl in H. exfalso. apply H. left. reflexivity.
    + reflexivity.
  -
    rewrite IHe1.
    rewrite IHe2.
    + reflexivity.
    + apply not_in_app_or in H. destruct H; assumption.
    + apply not_in_app_or in H. destruct H; assumption.
  -
    rewrite IHe1.
    rewrite IHe2.
    + reflexivity.
    + apply not_in_app_or in H. destruct H; assumption.
    + apply not_in_app_or in H. destruct H; assumption.
  -
    destruct (String.eqb_spec x x0); subst.
    + reflexivity.
    + rewrite IHe. reflexivity.
      simpl in H.
      intro Hin. apply H.
      apply in_in_remove.
      * assumption.
      * assumption.
  -
    destruct (String.eqb_spec x x0); subst.
    + rewrite IHe1.
      * reflexivity.
      * simpl in *.
        apply not_in_app_or in H. destruct H as [H1 H2]. exact H1.
    + rewrite IHe1.
      rewrite IHe2.
      * reflexivity.
      * simpl in *.
        apply not_in_app_or in H. destruct H as [H1 H2].
        intro Hin. apply H2. apply in_in_remove; assumption.
      * simpl in *.
        apply not_in_app_or in H. destruct H as [H1 H2].
        exact H1.
  -
    rewrite IHe1.
    rewrite IHe2.
    + reflexivity.
    + apply not_in_app_or in H. destruct H; assumption.
    + apply not_in_app_or in H. destruct H; assumption.
  -
    rewrite IHe. reflexivity.
    simpl in *. assumption.
  -
    rewrite IHe. reflexivity.
    simpl in *. assumption.
  -
    rewrite IHe1.
    rewrite IHe2.
    rewrite IHe3.
    simpl in *.
    + reflexivity.
    + apply not_in_app_or in H.
      destruct H as [H1 H2].
      fold free in *.
      apply not_in_app_or in H2. destruct H2 as [H3 H4]. assumption.
    + simpl in *.
      apply not_in_app_or in H. destruct H as [H1 H2].
      fold free in *.
      apply not_in_app_or in H2. destruct H2 as [H3 H4]. assumption.
    + simpl in *.
      apply not_in_app_or in H. destruct H as [H1 H2].
      fold free in *.
      apply not_in_app_or in H2. destruct H2 as [H3 H4]. assumption.
Qed.

Lemma subst_closed_m : forall e x v,
  free e = [] ->
  subst_m x v e = e.
Proof.
  intros e x v Hcl.
  apply subst_not_free_m.
  rewrite Hcl.
  intros [].
Qed.

Lemma mono_preserves_subst : forall Omega e em x v vm,
  closed_instance_env Omega ->
  mono_expr Omega e em ->
  mono_expr Omega v vm ->
  mono_expr Omega (subst_expr x v e) (subst_m x vm em).
Proof.
  intros Omega e em x v vm Hclosed He.
  generalize dependent vm.
  generalize dependent v.
  generalize dependent x.
  induction He; intros x0 v0 vm0 Hv; simpl; eauto.
  -
    destruct (String.eqb x0 x) eqn:Heq.
    + assumption.
    + constructor.
  -
    rewrite (subst_closed_m _ _ _ (Hclosed n ts em H)).
    constructor. assumption.
  -
    destruct (String.eqb_spec x0 x).
    + subst. constructor. assumption.
    + constructor. apply IHHe. assumption.
  -
    destruct (String.eqb_spec x0 x).
    + subst. constructor.
      * apply IHHe1. assumption.
      * assumption.
    + constructor.
      * apply IHHe1. assumption.
      * apply IHHe2. assumption.
Qed.

Lemma simulation_step : forall Omega x y em,
  closed_instance_env Omega ->
  step x y ->
  mono_expr Omega x em ->
  exists em', step_m em em' /\ mono_expr Omega y em'.
Proof.
  intros Omega x y em Hclosed Hstep.
  generalize dependent em.
  induction Hstep; intros em Hmono; inversion Hmono; subst.
  -
    inversion H2; subst.
    eexists. split.
    + apply STM_AppAbs.
      eapply mono_preserves_value; eassumption.
    + apply mono_preserves_subst; eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_App1. eassumption.
    + constructor; eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_App2; [ eapply mono_preserves_value; eassumption | eassumption ].
    + constructor; eassumption.
  -
    inversion H1; clear H1; subst.
    inversion H3; clear H3; subst.
    eexists. split.
    + apply STM_AddConstConst.
    + constructor.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_Add1. eassumption.
    + constructor; eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_Add2; [ eapply mono_preserves_value; eassumption | eassumption ].
    + constructor; eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_Let. eassumption.
    + constructor; eassumption.
  -
    eexists. split.
    + apply STM_Let_V.
      eapply mono_preserves_value; eassumption.
    + apply mono_preserves_subst; eassumption.
  -
    inversion H2; clear H2; subst.
    eexists. split.
    + apply STM_IfTrue.
    + eassumption.
  -
    inversion H2; clear H2; subst.
    eexists. split.
    + apply STM_IfFalse.
    + eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_If. eassumption.
    + constructor; eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_Pair1. eassumption.
    + constructor; eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_Pair2; [ eapply mono_preserves_value; eassumption | eassumption ].
    + constructor; eassumption.
  -
    inversion H2; subst.
    eexists. split.
    + apply STM_FstPair.
      * eapply mono_preserves_value; [ exact H | exact H4 ].
      * eapply mono_preserves_value; [ exact H0 | exact H6 ].
    + eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_Fst. eassumption.
    + constructor. eassumption.
  -
    inversion H2; subst.
    eexists. split.
    + apply STM_SndPair.
      * eapply mono_preserves_value; [ exact H | exact H4 ].
      * eapply mono_preserves_value; [ exact H0 | exact H6 ].
    + eassumption.
  -
    edestruct IHHstep as [? [? ?]]; [ eassumption | ].
    eexists. split.
    + apply STM_Snd. eassumption.
    + constructor. eassumption.
Qed.

Theorem simulation_multi :
  forall Omega e e',
    closed_instance_env Omega ->
    multistep e e' ->
    forall em,
      mono_expr Omega e em ->
      exists em',
        multistep_m em em' /\ mono_expr Omega e' em'.
Proof.
  intros Omega e e' Hclosed Hmulti.
  induction Hmulti as [x | x y z Hstep Hmulti IH].
  - intros em Hmono.
    exists em. split.
    + apply multi_refl.
    + assumption.
  - intros em Hmono.
    destruct (simulation_step Omega x y em Hclosed Hstep Hmono) as [em_y [Hstep_m Hmono_y]].
    destruct (IH em_y Hmono_y) as [em' [Hmulti_m Hmono_z]].
    exists em'. split.
    + eapply multi_step; eassumption.
    + assumption.
Qed.

Lemma more_specific_refl : forall t,
  more_specific t t.
Proof.
  intros.
  apply MS_Refl.
Qed.

Lemma more_specific_trans : forall t1 t2 t3,
  more_specific t1 t2 ->
  more_specific t2 t3 ->
  more_specific t1 t3.
Proof.
  intros t1 t2 t3 H12.
  generalize dependent t3.
  induction H12; intros t3 H23.
  -
    assumption.
  -
    inversion H23; subst; constructor.
  -
    inversion H23; subst; try constructor.
    + apply IHmore_specific1. apply MS_Refl.
    + apply IHmore_specific2. apply MS_Refl.
    + apply IHmore_specific1. assumption.
    + apply IHmore_specific2. assumption.
  -
    inversion H23; subst; try constructor.
    + assumption.
    + assumption.
    + apply IHmore_specific1. assumption.
    + apply IHmore_specific2. assumption.
  -
    inversion H23; subst; constructor.
  -
    inversion H23; subst; constructor.
  -
    inversion H23; subst; constructor.
Qed.

Lemma more_specific_scheme_trans : forall sch1 sch2 sch3,
  more_specific_scheme sch1 sch2 ->
  more_specific_scheme sch2 sch3 ->
  more_specific_scheme sch1 sch3.
Proof.
  intros.
  unfold more_specific_scheme in *.
  destruct sch1, sch2, sch3.
  apply more_specific_trans with (t2 := t0).
  + assumption.
  + assumption.
Qed.

Definition equally_specific_scheme (sch1 sch2 : type_scheme) : Prop :=
  more_specific_scheme sch1 sch2 /\ more_specific_scheme sch2 sch1.

Lemma equally_specific_scheme_refl : forall sch,
  equally_specific_scheme sch sch.
Proof.
  intros.
  unfold equally_specific_scheme. split; apply more_specific_scheme_refl.
Qed.

Lemma equally_specific_scheme_sym : forall sch1 sch2,
  equally_specific_scheme sch1 sch2 ->
  equally_specific_scheme sch2 sch1.
Proof.
  intros sch1 sch2 H.
  unfold equally_specific_scheme in H.
  intros.
  destruct sch1, sch2; subst.
  destruct H as [H12 H21]. split; assumption.
Qed.

Lemma equally_specific_scheme_trans : forall sch1 sch2 sch3,
  equally_specific_scheme sch1 sch2 ->
  equally_specific_scheme sch2 sch3 ->
  equally_specific_scheme sch1 sch3.
Proof.
  intros sch1 sch2 sch3 H12 H23.
  unfold equally_specific_scheme in *.
  destruct H12 as [H12_1 H12_2], H23 as [H23_1 H23_2].
  constructor.
  - apply more_specific_scheme_trans with (sch2 := sch2); [apply H12_1 | apply H23_1].
  - apply more_specific_scheme_trans with (sch2 := sch2); [apply H23_2 | apply H12_2].
Qed.

Lemma strictly_more_specific_scheme_irrefl : forall sch,
  ~ strictly_more_specific_scheme sch sch.
Proof.
  intros sch H.
  unfold strictly_more_specific_scheme in H.
  destruct H as [H1 H2].
  contradiction.
Qed.

Lemma strictly_more_specific_scheme_asym : forall sch1 sch2,
  strictly_more_specific_scheme sch1 sch2 ->
  ~ strictly_more_specific_scheme sch2 sch1.
Proof.
  intros sch1 sch2 H Hcontra.
  unfold strictly_more_specific_scheme in *.
  destruct H as [H12 H21], Hcontra as [H21' H12'].
  contradiction.
Qed.

Lemma strictly_more_specific_scheme_trans : forall sch1 sch2 sch3,
  strictly_more_specific_scheme sch1 sch2 ->
  strictly_more_specific_scheme sch2 sch3 ->
  strictly_more_specific_scheme sch1 sch3.
Proof.
  intros.
  unfold strictly_more_specific_scheme in *.
  destruct H as [H12 H21], H0 as [H23 H32].
  split.
  - apply more_specific_scheme_trans with (sch2 := sch2); assumption.
  - intros Hcontra.
    apply H32.
    eapply more_specific_scheme_trans with (sch2 := sch1).
    + exact Hcontra.
    + exact H12.
Qed.

Theorem most_specific_candidate_unique :
  forall catalog name ts sch1 sch2 em1 em2,
    In (name, sch1, em1) catalog ->
    In (name, sch2, em2) catalog ->
    (exists T1, instantiate sch1 ts T1) ->
    (exists T2, instantiate sch2 ts T2) ->
    is_most_specific_candidate catalog name ts sch1 ->
    is_most_specific_candidate catalog name ts sch2 ->
    ~ strictly_more_specific_scheme sch1 sch2 /\ ~ strictly_more_specific_scheme sch2 sch1.
Proof.
  intros catalog name ts sch1 sch2 em1 em2 H1 H2 Hinst1 Hinst2 Hcand1 Hcand2.
  split.
  -
    eapply Hcand2; try eassumption; reflexivity.
  -
    eapply Hcand1; try eassumption; reflexivity.
Qed.

Lemma mono_expr_exists :
  forall catalog Omega e,
    omega_covers catalog Omega e ->
    exists em, mono_expr Omega e em.
Proof.
  intros catalog Omega e.
  induction e; intros Hcov; simpl in *.
  - exists (EM_Const n). constructor.
  - exists (EM_Bool b). constructor.
  - exists (EM_String s). constructor.
  - exists (EM_Var x vars). constructor.
  -
    destruct Hcov as [Hvalid Hcalls].
    assert (Hin : In (x, vars) [(x, vars)]) by (simpl; auto).
    destruct (Hcalls x vars Hin) as [em Hin_om].
    exists em. constructor. assumption.
  -
    destruct Hcov as [Hvalid Hcalls].
    assert (Hcov1 : omega_covers catalog Omega e1).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. left. assumption. }
    assert (Hcov2 : omega_covers catalog Omega e2).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. right. assumption. }
    destruct (IHe1 Hcov1) as [em1 Hmono1].
    destruct (IHe2 Hcov2) as [em2 Hmono2].
    exists (EM_App em1 em2). constructor; assumption.
  -
    destruct Hcov as [Hvalid Hcalls].
    assert (Hcov1 : omega_covers catalog Omega e1).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. left. assumption. }
    assert (Hcov2 : omega_covers catalog Omega e2).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. right. assumption. }
    destruct (IHe1 Hcov1) as [em1 Hmono1].
    destruct (IHe2 Hcov2) as [em2 Hmono2].
    exists (EM_Add em1 em2). constructor; assumption.
  -
    destruct (IHe Hcov) as [em Hmono].
    exists em. constructor. assumption.
  -
    destruct (IHe Hcov) as [em Hmono].
    exists (EM_Abs x t em). constructor. assumption.
  -
    destruct Hcov as [Hvalid Hcalls].
    assert (Hcov1 : omega_covers catalog Omega e1).
    { split; [assumption |].
      intros n0 ts0 Hin. apply Hcalls. apply in_or_app. left. assumption. }
    assert (Hcov2 : omega_covers catalog Omega e2).
    { split; [assumption |].
      intros n0 ts0 Hin. apply Hcalls. apply in_or_app. right. assumption. }
    destruct (IHe1 Hcov1) as [em1 Hmono1].
    destruct (IHe2 Hcov2) as [em2 Hmono2].
    exists (EM_Let x ts em1 em2). constructor; assumption.
  -
    destruct Hcov as [Hvalid Hcalls].
    assert (Hcov1 : omega_covers catalog Omega e1).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. left. assumption. }
    assert (Hcov2 : omega_covers catalog Omega e2).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. right. assumption. }
    destruct (IHe1 Hcov1) as [em1 Hmono1].
    destruct (IHe2 Hcov2) as [em2 Hmono2].
    exists (EM_Pair em1 em2). constructor; assumption.
  -
    destruct (IHe Hcov) as [em Hmono].
    exists (EM_Fst em). constructor. assumption.
  -
    destruct (IHe Hcov) as [em Hmono].
    exists (EM_Snd em). constructor. assumption.
  -
    destruct Hcov as [Hvalid Hcalls].
    assert (Hcov1 : omega_covers catalog Omega e1).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. left. assumption. }
    destruct (IHe1 Hcov1) as [em1 Hmono1].
    assert (Hcov2 : omega_covers catalog Omega e2).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. right.
      apply in_or_app. left. assumption. }
    assert (Hcov3 : omega_covers catalog Omega e3).
    { split; [assumption |].
      intros n ts Hin. apply Hcalls. apply in_or_app. right.
      apply in_or_app. right. assumption. }
    destruct (IHe2 Hcov2) as [em2 Hmono2].
    destruct (IHe3 Hcov3) as [em3 Hmono3].
    exists (EM_If em1 em2 em3). constructor; assumption.
Qed.

Lemma build_omega_for_calls :
  forall catalog calls,
    (forall n ts, In (n, ts) calls -> exists em, select_instance catalog n ts em) ->
    exists Omega,
      valid_monomorphization catalog Omega /\
      (forall n ts, In (n, ts) calls -> exists em, In (n, ts, em) Omega).
Proof.
  intros catalog calls.
  induction calls as [| [n0 ts0] rest IH]; intros Hcalls.
  - exists []. split.
    + intros name ts em Hin. inversion Hin.
    + intros name ts Hin. inversion Hin.
  - assert (Hrest : forall n ts, In (n, ts) rest -> exists em, select_instance catalog n ts em).
    { intros n ts Hin. apply Hcalls. right. assumption. }
    destruct (IH Hrest) as [Omega_rest [Hvalid_rest Hcov_rest]].
    assert (Hhead : exists em, select_instance catalog n0 ts0 em).
    { apply Hcalls. left. reflexivity. }
    destruct Hhead as [em0 Hsel0].
    exists ((n0, ts0, em0) :: Omega_rest).
    split.
    + intros name ts em Hin.
      destruct Hin as [Heq | Hin_rest].
      * inversion Heq; subst.
        unfold select_instance in Hsel0. assumption.
      * apply Hvalid_rest. assumption.
    + intros name ts Hin.
      destruct Hin as [Heq | Hin_rest].
      * inversion Heq; subst.
        exists em0. left. reflexivity.
      * destruct (Hcov_rest name ts Hin_rest) as [em Hin_om].
        exists em. right. assumption.
Qed.

Lemma omega_existence :
  forall catalog e,
    catalog_covers catalog e ->
    exists Omega, omega_covers catalog Omega e.
Proof.
  intros catalog e Hcov.
  unfold catalog_covers in Hcov.
  destruct (build_omega_for_calls catalog (collect_ovars e) Hcov) as [Omega [Hvalid Hcov_calls]].
  exists Omega.
  unfold omega_covers.
  split; assumption.
Qed.

Theorem monomorphization_existence :
  forall catalog e,
    catalog_covers catalog e ->
    exists Omega em,
      valid_monomorphization catalog Omega /\
      mono_expr Omega e em.
Proof.
  intros catalog e Hcov.
  destruct (omega_existence catalog e Hcov) as [Omega Homega].
  destruct (mono_expr_exists catalog Omega e Homega) as [em Hmono].
  exists Omega, em.
  split.
  - destruct Homega as [Hvalid _]. exact Hvalid.
  - exact Hmono.
Qed.

Theorem monomorphization_soundness_with_coverage :
  forall Gamma Delta e t Omega em Gamma_m catalog,
    has_type Gamma Delta e t ->
    omega_covers catalog Omega e ->
    instance_env_matches Delta Omega ->
    context_matches Gamma Gamma_m ->
    mono_expr Omega e em ->
    (forall n tvs t0 ts Tinst em0,
      instantiate (Ty_Forall tvs t0) ts Tinst ->
      In (n, ts, em0) Omega ->
      has_type_m [] em0 Tinst) ->
    has_type_m Gamma_m em t.
Proof.
  intros Gamma Delta e t Omega em Gamma_m catalog Htyp Hcov Hmatch_env Hmatch_ctx Hmono Hinst_valid.
  destruct Hcov as [Hvalid _].
  eapply monomorphization_preserves_typing; eassumption.
Qed.

Theorem end_to_end_soundness :
  forall catalog Delta e t,

    has_type [] Delta e t ->

    catalog_covers catalog e ->

    catalog_conforms catalog Delta ->
    (forall Omega, valid_monomorphization catalog Omega ->
       forall n tvs t0 ts Tinst em0,
         instantiate (Ty_Forall tvs t0) ts Tinst ->
         In (n, ts, em0) Omega ->
         has_type_m [] em0 Tinst) ->

    exists Omega em,

      mono_expr Omega e em /\

      has_type_m [] em t /\

      (forall em', multistep_m em em' -> ~ stuck_m em').
Proof.
  intros catalog Delta e t Htyp Hcov Hmatch_env Hinst_valid.
  destruct (omega_existence catalog e Hcov) as [Omega Homega].
  destruct (mono_expr_exists catalog Omega e Homega) as [em Hmono].
  exists Omega, em.
  split.
  -
    exact Hmono.
  -
    assert (Htyp_m : has_type_m [] em t).
    {
      eapply monomorphization_soundness_with_coverage with
        (catalog := catalog) (Delta := Delta) (Gamma := []); try eassumption.
      - apply catalog_conforms_implies_matches with (catalog := catalog).
        + exact Hmatch_env.
        + destruct Homega as [Hvalid _]. exact Hvalid.
      - constructor.
      - apply Hinst_valid.
        destruct Homega as [Hvalid _]. exact Hvalid.
    }
    split.
    + exact Htyp_m.
    +
      intros em' Hmulti.
      eapply soundness_m; eassumption.
Qed.
