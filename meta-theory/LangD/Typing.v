Require Import Overloading.LangD.Definitions.
Require Import Overloading.LangD.Maps.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Lists.List.
From Stdlib Require PeanoNat.
Require Import Stdlib.Strings.String.
Import ListNotations.

Lemma canonical_form_tuple :
  forall e t1 t2,
    has_type [] empty e (Ty_Tuple t1 t2) ->
    value e ->
    exists e1 e2,
      e = E_Pair e1 e2.
Proof.
  intros e t1 t2 Htyp Hval.
  inversion Hval; subst; try (inversion Htyp; subst).
  exists e1, e2. reflexivity.
Qed.

Lemma weakening_Delta :
  forall Gamma Delta Delta' e tau,
    has_type Gamma Delta e tau ->
    includedin Delta Delta' ->
    has_type Gamma Delta' e tau.
Proof.
  intros Gamma Delta Delta' e tau Htyp_e Hinc.
  generalize dependent Delta'.
  induction Htyp_e; intros Delta' Hinc.
  - constructor.
  - constructor.
  - constructor.
  - apply T_Var with (sch := sch).
    + assumption.
    + assumption.
  - apply T_Over with (sch := sch).
    + unfold property_lookup in *.
      intros. apply Hinc. assumption.
    + assumption.
  - apply T_App with (t1 := t1).
    + apply IHHtyp_e1. assumption.
    + apply IHHtyp_e2. assumption.
  - apply T_Add; [apply IHHtyp_e1 | apply IHHtyp_e2]; assumption.
  - apply T_Property.
    + apply IHHtyp_e. apply includedin_update. assumption.
  - apply T_Abs with (t2 := t2).
    apply IHHtyp_e. assumption.
  - apply T_Let with (t1 := t1) (t2 := t2).
    + intros ts_args Tinst Hinst.
      apply H0 with (ts_args := ts_args); assumption.
    + apply IHHtyp_e; assumption.
  - apply T_If with (t := t).
    + apply IHHtyp_e1. assumption.
    + apply IHHtyp_e2. assumption.
    + apply IHHtyp_e3. assumption.
  - apply T_Pair.
    + apply IHHtyp_e1. assumption.
    + apply IHHtyp_e2. assumption.
  - apply T_Fst with (t2 := t2).
    apply IHHtyp_e. assumption.
  - apply T_Snd with (t1 := t1).
    apply IHHtyp_e. assumption.
Qed.

Lemma variable_lookup_app : forall Gamma Gamma' x t,
  variable_lookup (Gamma ++ Gamma') x t ->
  variable_lookup Gamma x t \/ variable_lookup Gamma' x t.
Proof.
  induction Gamma as [| [y ty] Gamma IH]; intros Gamma' x t Hlook; simpl in *.
  - right. assumption.
  - inversion Hlook; subst.
    + left. constructor.
    + apply IH in H5. destruct H5 as [H1 | H2].
      * left. apply VL_There; assumption.
      * right. assumption.
Qed.

Lemma variable_lookup_in : forall Gamma x t,
  variable_lookup Gamma x t ->
  In (x, t) Gamma.
Proof.
  intros Gamma x t Hlook.
  induction Hlook; simpl.
  - left. reflexivity.
  - right. assumption.
Qed.

Lemma weakening :
  forall Gamma Gamma' Delta e tau,
    has_type Gamma Delta e tau ->
    has_type (List.app Gamma Gamma') Delta e tau.
Proof.
  intros Gamma Gamma' Delta e tau Htyp.
  generalize dependent Gamma'.
  induction Htyp; intros.
  - constructor.
  - constructor.
  - constructor.
  - apply T_Var with (sch := sch).
    + apply variable_lookup_weakening.
      assumption.
    + assumption.
  - apply T_Over with (sch := sch).
    unfold property_lookup in *.
    + assumption.
    + assumption.
  - apply T_App with (t1 := t1).
    + apply IHHtyp1.
    + apply IHHtyp2.
  - apply T_Add; [apply IHHtyp1 | apply IHHtyp2]; assumption.
  - apply T_Property.
    + apply IHHtyp.
  - apply T_Abs with (t2 := t2).
    apply IHHtyp.
  - apply T_Let with (t1 := t1) (t2 := t2).
    + intros ts_args Tinst Hinst.
      apply H0 with (ts_args := ts_args); assumption.
    + apply IHHtyp.
  - apply T_If with (t := t).
    + apply IHHtyp1.
    + apply IHHtyp2.
    + apply IHHtyp3.
  - apply T_Pair.
    + apply IHHtyp1.
    + apply IHHtyp2.
  - apply T_Fst with (t2 := t2).
    apply IHHtyp.
  - apply T_Snd with (t1 := t1).
    apply IHHtyp.
Qed.

Lemma weakening_empty :
  forall Gamma Delta e tau,
    has_type [] Delta e tau ->
    has_type Gamma Delta e tau.
Proof.
  intros Gamma Delta e tau H.
  apply weakening with (Gamma' := Gamma) in H.
  exact H.
Qed.

Lemma weakening_Delta_empty :
  forall Gamma Delta e tau,
    has_type Gamma empty e tau ->
    has_type Gamma Delta e tau.
Proof.
  intros.
  apply weakening_Delta with (Delta' := Delta) in H.
  - assumption.
  - unfold includedin. intros. inversion H0.
Qed.

Lemma canonical_form_arrow :
  forall e t1 t2,
    has_type [] empty e (Ty_Arrow t1 t2) ->
    value e ->
    exists x t e1,
      e = E_Abs x t e1.
Proof.
  intros e t1 t2 Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists x, t1, e0. reflexivity.
Qed.

Lemma canonical_form_nat :
  forall e,
    has_type [] empty e Ty_Nat ->
    value e ->
    exists n,
      e = E_Const n.
Proof.
  intros e Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists n. reflexivity.
Qed.

Lemma canonical_form_bool :
  forall e,
    has_type [] empty e Ty_Bool ->
    value e ->
      (e = E_Bool true) \/ (e = E_Bool false).
Proof.
  intros e Htyp Hval.
  destruct Hval; auto; try (inversion Htyp).
  inversion Htyp; subst.
  destruct b.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma typed_canonical_form_arrow :
  forall e t1 t2,
    has_type [] empty e (Ty_Arrow t1 t2) ->
    value e ->
    exists x t e1,
      e = E_Abs x t e1.
Proof.
  intros e t1 t2 Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists x, t1, e0. split; reflexivity.
Qed.

Fixpoint property_free (e: expr) : Prop :=
  match e with
  | E_Const _ | E_Bool _ | E_String _ => True
  | E_Var _ _ => True
  | E_OVar _ _ => True
  | E_App e1 e2 | E_Add e1 e2 | E_Pair e1 e2 => property_free e1 /\ property_free e2
  | E_Property _ _ _ _ => False
  | E_Abs _ _ e | E_Fst e | E_Snd e => property_free e
  | E_Let _ _ e1 e2 => property_free e1 /\ property_free e2
  | E_If e1 e2 e3 => property_free e1 /\ property_free e2 /\ property_free e3
  end.

Theorem progress :
  forall e t,
    property_free e ->
    has_type [] empty e t ->
    value e \/ (exists e', step e e').
Proof.
    intros e t Hfree Htyp.
    remember [] as Gamma.
    remember empty as Delta.

    induction Htyp; subst; simpl in Hfree.
    - left. constructor.
    - left. constructor.
    - left. constructor.
    - inversion H; subst.
    - unfold property_lookup in H.
      inversion H.
    -
      destruct Hfree as [Hf1 Hf2].
      right.
      destruct (IHHtyp1 Hf1 eq_refl eq_refl) as [Hval1 | [e1' Hstep1]].
      + destruct (IHHtyp2 Hf2 eq_refl eq_refl) as [Hval2 | [e2' Hstep2]].
        * destruct (canonical_form_arrow _ _ _ Htyp1 Hval1) as [x [t [body]]].
          subst. exists (subst_expr x e2 body). constructor. assumption.
        * exists (E_App e1 e2'). constructor. assumption.
          assumption.
      + exists (E_App e1' e2). constructor. assumption.
    -
      destruct Hfree as [Hf1 Hf2].
      right.
      destruct (IHHtyp1 Hf1 eq_refl eq_refl) as [Hval1 | [e1' Hstep1]];
        destruct (IHHtyp2 Hf2 eq_refl eq_refl) as [Hval2 | [e2' Hstep2]].
      + destruct (canonical_form_nat _ Htyp1 Hval1) as [n].
        destruct (canonical_form_nat _ Htyp2 Hval2) as [m].
        subst. exists (E_Const (n + m)). constructor.
      + exists (E_Add e1 e2'). constructor. assumption. assumption.
      + exists (E_Add e1' e2). constructor. assumption.
      + exists (E_Add e1' e2). constructor. assumption.
    -
      contradiction.
    -
      left. constructor.
    -
      destruct Hfree as [Hf1 Hf2].
      right.
      destruct (scheme_has_instance ts t1) as [Tinst Hinst].
      destruct (H0 (repeat Ty_Nat (List.length ts)) Tinst Hinst Hf1 eq_refl eq_refl) as [Hval1 | [e1' Hstep1]].
      + exists (subst_expr x e1 e2). constructor. assumption.
      + exists (E_Let x ts e1' e2). constructor. assumption.
    -
      destruct Hfree as [Hf1 [Hf2 Hf3]].
      right.
      destruct (IHHtyp1 Hf1 eq_refl eq_refl) as [Hval1 | [e1' Hstep1]].
      + destruct (canonical_form_bool _ Htyp1 Hval1) as [Heq | Heq]; subst.
        * exists e2. constructor.
        * exists e3. constructor.
      + exists (E_If e1' e2 e3). constructor. assumption.
    -
      destruct Hfree as [Hf1 Hf2].
      destruct (IHHtyp1 Hf1 eq_refl eq_refl) as [Hval1 | [e1' Hstep1]].
      + destruct (IHHtyp2 Hf2 eq_refl eq_refl) as [Hval2 | [e2' Hstep2]].
        * left. constructor. assumption. assumption.
        * right. exists (E_Pair e1 e2'). constructor. assumption. assumption.
      + right. exists (E_Pair e1' e2). constructor. assumption.
    -
      destruct (IHHtyp Hfree eq_refl eq_refl) as [Hval | [e' Hstep]].
      + destruct (canonical_form_tuple _ _ _ Htyp Hval) as [e1 [e2 Heq]].
        subst. right. exists e1. constructor.
        inversion Hval; subst. assumption.
        inversion Hval; subst. assumption.
      + right. exists (E_Fst e'). constructor. assumption.
    -
      destruct (IHHtyp Hfree eq_refl eq_refl) as [Hval | [e' Hstep]].
      + destruct (canonical_form_tuple _ _ _ Htyp Hval) as [e1 [e2 Heq]].
        subst. right. exists e2. constructor.
        inversion Hval; subst. assumption.
        inversion Hval; subst. assumption.
      + right. exists (E_Snd e'). constructor. assumption.
Qed.

Lemma neq_sym : forall x y : string,
    x <> y -> y <> x.
Proof.
  intros x y Hneq Hxy. apply Hneq. symmetry. assumption.
Qed.

Lemma eqb_false : forall x y : string,
    x <> y ->
    String.eqb x y = false.
Proof.
  intros x y Hneq.
  apply String.eqb_neq. assumption.
Qed.

Lemma context_shadow_prefix : forall prefix Gamma Delta e T x t1 t2,
  has_type (prefix ++ (x, t1) :: (x, t2) :: Gamma) Delta e T ->
  has_type (prefix ++ (x, t1) :: Gamma) Delta e T.
Proof.
  intros prefix Gamma Delta e T x t1 t2 Htyp.
  remember (prefix ++ (x, t1) :: (x, t2) :: Gamma) as Gamma0.
  generalize dependent prefix.
  generalize dependent Gamma.
  generalize dependent t2.
  generalize dependent t1.
  generalize dependent x.
   induction Htyp; intros x0 t1' t2' Gamma' prefix' Heq; subst.
  - constructor.
  - constructor.
  - constructor.
  - apply T_Var with (sch := sch).
    eapply variable_lookup_shadow_prefix.
    exact H.
    assumption.
  - apply T_Over with (sch := sch).
    assumption.
    assumption.
  - eapply T_App.
    + eapply IHHtyp1. reflexivity.
    + eapply IHHtyp2. reflexivity.
  - apply T_Add; [eapply IHHtyp1; reflexivity | eapply IHHtyp2; reflexivity].
  - apply T_Property.
    eapply IHHtyp; reflexivity.
  - apply T_Abs. eapply IHHtyp with (prefix := (x, Ty_Forall [] t1) :: prefix').
    reflexivity.
  - eapply T_Let.
    + intros ts_args Tinst Hinst.
      eapply (H0 ts_args Tinst Hinst) with (prefix := prefix'). reflexivity.
    + simpl. eapply IHHtyp with (prefix := (x, Ty_Forall ts t1) :: prefix').
      reflexivity.
  - eapply T_If; [eapply IHHtyp1; reflexivity | eapply IHHtyp2; reflexivity | eapply IHHtyp3; reflexivity].
  - apply T_Pair; [eapply IHHtyp1; reflexivity | eapply IHHtyp2; reflexivity].
  - eapply T_Fst. eapply IHHtyp. reflexivity.
  - eapply T_Snd. eapply IHHtyp. reflexivity.
Qed.

Lemma context_shadow : forall Gamma Delta e T x t1 t2,
  has_type ((x, t1) :: (x, t2) :: Gamma) Delta e T ->
  has_type ((x, t1) :: Gamma) Delta e T.
Proof.
  intros.
  apply (context_shadow_prefix []) with (t2 := t2).
  exact H.
Qed.

Lemma update_context_switch_impossible :
  forall {A: Type} Gamma (x1 x2: string) (t1 t2: A),
    x1 <> x2 ->
    (x2, t2) :: (x1, t1) :: Gamma <>
    (x1, t1) :: (x2, t2) :: Gamma.
Proof.
  intros A Gamma x1 x2 t1 t2 Hneq.
  unfold not.
  intros H. inversion H; subst. apply Hneq. reflexivity.
Qed.

Lemma context_permute_prefix : forall prefix Gamma Delta e T x1 x2 t1 t2,
  x1 <> x2 ->
  has_type (prefix ++ (x1, t1) :: (x2, t2) :: Gamma) Delta e T ->
  has_type (prefix ++ (x2, t2) :: (x1, t1) :: Gamma) Delta e T.
Proof.
  intros prefix Gamma Delta e T x1 x2 t1 t2 Hneq Htyp.
  remember (prefix ++ (x1, t1) :: (x2, t2) :: Gamma) as Gamma0.
  generalize dependent prefix.
  generalize dependent Gamma.
  generalize dependent t2.
  generalize dependent t1.
  generalize dependent x1.
  generalize dependent x2.
  induction Htyp; intros x2 x1 Hneq t1' t2' Gamma' prefix' Heq; subst.
  - constructor.
  - constructor.
  - constructor.
  - apply T_Var with (sch := sch).
    eapply variable_lookup_permute_prefix; eassumption.
    assumption.
  - apply T_Over with (sch := sch).
    + assumption.
    + assumption.
  - eapply T_App.
    + eapply IHHtyp1.
      * assumption.
      * reflexivity.
    + eapply IHHtyp2.
      * assumption.
      * reflexivity.
  - apply T_Add.
    + eapply IHHtyp1. assumption. reflexivity.
    + eapply IHHtyp2. assumption. reflexivity.
  - apply T_Property.
    eapply IHHtyp. assumption. reflexivity.
  - apply T_Abs.
    apply IHHtyp with (prefix := (x, Ty_Forall [] t1) :: prefix').
    assumption.
    reflexivity.
  - eapply T_Let.
    + intros ts_args Tinst Hinst.
      eapply (H0 ts_args Tinst Hinst) with (prefix := prefix').
      assumption. reflexivity.
    + eapply IHHtyp with (prefix := (x, Ty_Forall ts t1) :: prefix').
      assumption. reflexivity.
  - eapply T_If.
    + eapply IHHtyp1. assumption. reflexivity.
    + apply IHHtyp2. assumption. reflexivity.
    + apply IHHtyp3. assumption. reflexivity.
  - apply T_Pair.
    + eapply IHHtyp1. assumption. reflexivity.
    + eapply IHHtyp2. assumption. reflexivity.
  - eapply T_Fst.
    eapply IHHtyp. assumption. reflexivity.
  - eapply T_Snd.
    eapply IHHtyp. assumption. reflexivity.
Qed.

Lemma context_permute : forall Gamma Delta e T x1 x2 t1 t2,
  x1 <> x2 ->
  has_type ((x1, t1) :: (x2, t2) :: Gamma) Delta e T ->
  has_type ((x2, t2) :: (x1, t1) :: Gamma) Delta e T.
Proof.
  intros Gamma Delta e T x1 x2 t1 t2 Hneq Htyp.
  apply (context_permute_prefix []).
  - assumption.
  - exact Htyp.
Qed.

Lemma substitution_preserves_typing : forall Gamma Delta x sch e v T,
  has_type (update_context Gamma x sch) Delta e T ->
  (forall ts Tinst, instantiate sch ts Tinst -> has_type [] empty v Tinst) ->
  has_type Gamma Delta (subst_expr x v e) T.
Proof.
  intros Gamma Delta x sch e v T Htyp_e Htyp_v.
  generalize dependent Gamma.
  generalize dependent Delta.
  generalize dependent T.
  generalize dependent sch.

  induction e; intros sch Htyp_v T Delta Gamma Htyp_e; simpl; inversion Htyp_e; subst.
  -
    constructor.
  -
    constructor.
  -
    constructor.
  -
    simpl.
    destruct (String.eqb_spec x0 x).
    +
      subst.
      rewrite String.eqb_refl.
      unfold update_context in *.
      inversion H3; subst.
      * apply Htyp_v in H5.
        apply weakening_empty. apply weakening_Delta_empty. assumption.
      * contradiction H6. reflexivity.
    +
      rewrite eqb_false; try assumption.
      eapply T_Var.
      unfold update_context in H3.
      * inversion H3; subst.
        contradiction n. reflexivity.
        eassumption.
      * assumption.
      * symmetry. assumption.
  - apply T_Over with (sch := sch0).
    + assumption.
    + assumption.
  -
    apply T_App with (t1 := t1); try assumption.
    + eapply IHe1.
      * eassumption.
      * assumption.
    + eapply IHe2.
      * eassumption.
      * assumption.
  -
    apply T_Add; [eapply IHe1 | eapply IHe2]; try eassumption.
  -
    eapply T_Property.
    eapply IHe; eassumption.
  -
    apply T_Abs with (t2 := t2).
    destruct (String.eqb_spec x0 x); subst.
    +
      rewrite String.eqb_refl.
      unfold update_context in H5.
      apply context_shadow in H5.
      assumption.
    +
      rewrite eqb_false; try assumption.
      eapply IHe. eassumption.
      unfold update_context in *.
      apply context_permute with (x1 := x0) (x2 := x); try assumption.
      symmetry. assumption.
  -
    apply T_Let with (t1 := t1) (t2 := T).
    + intros ts_args Tinst Hinst.
      eapply IHe1; [ eassumption | apply (H6 ts_args Tinst Hinst) ].
    + simpl.
      destruct (String.eqb_spec x0 x).
      *
        subst. rewrite eqb_refl.
        unfold update_context in *.
        apply context_shadow in H7.
        assumption.
      *
        rewrite eqb_false; try assumption.
        eapply IHe2.
        unfold update_context in *.
        eassumption.
        apply context_permute with (x1 := x0) (x2 := x); try assumption.
        symmetry. assumption.
  -
    apply T_Pair with (t1 := t1) (t2 := t2).
    + eapply IHe1. try eassumption. eassumption.
    + eapply IHe2. try eassumption. eassumption.
  -
    apply T_Fst with (t2 := t2).
    eapply IHe. eassumption.
    assumption.
  -
    apply T_Snd with (t1 := t1).
    eapply IHe. eassumption.
    assumption.
  -
    apply T_If with (t := T); try assumption.
    + eapply IHe1. eassumption. assumption.
    + eapply IHe2. eassumption. assumption.
    + eapply IHe3. eassumption. assumption.
Qed.

Lemma apply_type_env_lookup : forall Gamma x t b repl,
  variable_lookup Gamma x t ->
  variable_lookup (apply_type_env b repl Gamma) x (apply_type_scheme b repl t).
Proof.
  intros Gamma x t b repl H.
  unfold apply_type_env.
  induction H; simpl.
  - constructor.
  - constructor. assumption. assumption.
Qed.

Lemma apply_type_env_update : forall (Gamma : context) x t b (repl : type),
  apply_type_env b repl (update_context Gamma x t) =
  update_context (apply_type_env b repl Gamma) x (apply_type_scheme b repl t).
Proof.
  intros Gamma x t repl.
  unfold apply_type_env, update.
  simpl. unfold update_context. simpl. reflexivity.
Qed.

Fixpoint subst_type_context (c: tyvar) (repl: type) (Gamma: context) : context :=
  match Gamma with
  | [] => []
  | (x, t) :: rest => (x, apply_type_scheme c repl t) :: subst_type_context c repl rest
  end.

Definition subst_type_Delta (c: tyvar) (repl: type) (Delta: properties) : properties :=
  fun name =>
    match Delta name with
    | Some sch => Some (apply_type_scheme c repl sch)
    | None => None
    end.

Lemma substitution_preserves_typing_over : forall Gamma Delta x sch e v T,
  has_type Gamma (update_properties Delta x sch) e T ->
  (forall ts Tinst, instantiate sch ts Tinst -> has_type [] empty v Tinst) ->
  has_type Gamma Delta (subst_over x v e) T.
Proof.
  intros Gamma Delta x sch e v T Htyp_e Htyp_v.
  generalize dependent Gamma.
  generalize dependent Delta.
  generalize dependent T.

  induction e; intros T Delta Gamma Htyp_e; simpl; inversion Htyp_e; subst.
  -
    constructor.
  -
    constructor.
  -
    constructor.
  -
    simpl.
    eapply T_Var.
    + eassumption.
    + assumption.
  -
    simpl.
    destruct (String.eqb_spec x x0); subst.
    + unfold update_properties, property_lookup in H3.

      rewrite update_eq in H3. inversion H3. subst.

      apply Htyp_v in H5.

      apply weakening_empty.
      apply weakening_Delta_empty.
      assumption.
    +
      apply T_Over with (sch := sch0).
      * unfold update_properties, property_lookup in H3.
        rewrite update_neq in H3.
        -- assumption.
        -- symmetry. assumption.
      * assumption.
  -
    apply T_App with (t1 := t1); try assumption.
    + apply IHe1. assumption.
    + apply IHe2. assumption.
  -
    apply T_Add; [apply IHe1 | apply IHe2]. assumption.
    assumption.
  -
    simpl.
    destruct (String.eqb_spec x n); subst.
    + apply T_Property.
      unfold update_properties in *.
      rewrite update_shadow in H6.
      assumption.
    + apply T_Property.
      apply IHe.
      unfold update_properties in *.
      rewrite update_permute in H6.
      * assumption.
      * assumption.
  -
    apply T_Abs with (t2 := t2).
    apply IHe.
    + assumption.
  -
    apply T_Let with (t1 := t1) (t2 := T).
    + intros ts_args Tinst Hinst.
      apply IHe1.
      apply (H6 ts_args Tinst Hinst).
    + apply IHe2.
      assumption.
  -
    apply T_Pair with (t1 := t1) (t2 := t2).
    + apply IHe1. assumption.
    + apply IHe2. assumption.
  -
    apply T_Fst with (t2 := t2).
    apply IHe. assumption.
  -
    apply T_Snd with (t1 := t1).
    apply IHe. assumption.
  -
    apply T_If with (t := T); try assumption.
    + apply IHe1; assumption.
    + apply IHe2. try assumption.
    + apply IHe3. try assumption.
Qed.

Lemma instantiate_nil : forall sch ts T,
  instantiate (Ty_Forall [] sch) ts T ->
  T = sch /\ ts = [].
Proof.
  intros sch ts T H.
  unfold instantiate in H.
  destruct ts; simpl in H.
  - inversion H; subst. split; reflexivity.
  - discriminate.
Qed.

Lemma instantiate_unique : forall tvs sch ts T1 T2,
  instantiate (Ty_Forall tvs sch) ts T1 ->
  instantiate (Ty_Forall tvs sch) ts T2 ->
  T1 = T2.
Proof.
  intros tvs sch ts T1 T2 H1 H2.
  unfold instantiate in *.
  rewrite H1 in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma instantiate_unique' : forall sch ts T1 T2,
  instantiate sch ts T1 ->
  instantiate sch ts T2 ->
  T1 = T2.
Proof.
  intros [tvs sch] ts T1 T2 H1 H2.
  unfold instantiate in *.
  rewrite H1 in H2.
  inversion H2.
  reflexivity.
Qed.

Theorem preservation :
  forall e e' t,
    has_type [] empty e t ->
    step e e' ->
    has_type [] empty e' t.
Proof.
  intros e e' t Htyp Hstep.
  generalize dependent t.

  induction Hstep; intros t' Htyp.

  -
    inversion Htyp; subst.
    inversion H4; subst.
    eapply substitution_preserves_typing.
    eassumption.
    intros ts0 Tinst Hinst.
    apply instantiate_nil in Hinst. destruct Hinst as [Heq _]. subst.
    assumption.

  -
    inversion Htyp; subst.
    eapply T_App.
    + eapply IHHstep. eassumption.
    + assumption.

  -
    inversion Htyp; subst.
    eapply T_App.
    + eassumption.
    + apply IHHstep. assumption.

  -
    inversion Htyp; subst.
    constructor.

  -
    inversion Htyp; subst.
    econstructor.
    eapply IHHstep. eassumption.
    assumption.

  -
    inversion Htyp; subst.
    econstructor.
    assumption.
    eapply IHHstep. eassumption.

  -
    inversion Htyp; subst.
    econstructor.
    + intros ts_args Tinst Hinst.
      eapply IHHstep. eauto.
    + assumption.

  -
    inversion Htyp; subst.
    eapply substitution_preserves_typing.
    + eassumption.
    + assumption.

  -
    inversion Htyp; subst.
    assumption.

  -
    inversion Htyp; subst.
    assumption.

  -
    inversion Htyp; subst.
    eauto.

  -
    inversion Htyp; subst.
    eauto.

  -
    inversion Htyp; subst.
    eauto.

  -
    inversion Htyp; subst.
    inversion H4; subst.
    assumption.

  -
    inversion Htyp; subst.
    eauto.

  -
    inversion Htyp; subst.
    inversion H4; subst.
    assumption.

  -
    inversion Htyp; subst.
    eauto.
Qed.

Lemma property_free_subst : forall x v e,
  property_free v ->
  property_free e ->
  property_free (subst_expr x v e).
Proof.
  intros x v e Hv.
  induction e; intros He; simpl in *; auto.
  - destruct (String.eqb x x0); auto.
  - destruct He as [He1 He2]; auto.
  - destruct He as [He1 He2]; auto.
  - destruct (String.eqb x x0); simpl; auto.
  - destruct (String.eqb x x0); simpl; auto.
    + destruct He as [He1 He2]; auto.
    + destruct He as [He1 He2]; auto.
  - destruct He as [He1 He2].
    split.
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - destruct He as [He1 [He2 He3]]; auto.
Qed.

Lemma step_preserves_property_free : forall e e',
  step e e' ->
  property_free e ->
  property_free e'.
Proof.
  intros e e' Hstep.
  induction Hstep; intros Hfree; simpl in *; try tauto.
  - destruct Hfree as [Habs Hv]. simpl in Habs.
    apply property_free_subst; assumption.
  - destruct Hfree as [H1 H2].
    apply property_free_subst; assumption.
Qed.

Definition stuck (t: expr) : Prop :=
  (normal_form step) t /\ not (value t).

Theorem soundness :
  forall e e' t,
    property_free e ->
    has_type [] empty e t ->
    (multistep e e') ->
    not (stuck e').
Proof.
  intros e e' t Hfree Htyp Hmulti.
  revert t Hfree Htyp.
  induction Hmulti; intros t0 Hfree0 Htyp0 [Hnf Hnotval].
  -
    apply Hnotval.
    destruct (progress x t0 Hfree0 Htyp0) as [Hval | [e' Hstep]].
    + assumption.
    + exfalso. apply Hnf. exists e'. assumption.
  -
    assert (Hfree_y : property_free y) by (eapply step_preserves_property_free; eassumption).
    assert (Htyp_y : has_type [] empty y t0) by (eapply preservation; eassumption).
    apply (IHHmulti t0 Hfree_y Htyp_y). split; assumption.
Qed.

Lemma variable_lookup_unique : forall Gamma x t1 t2,
    variable_lookup Gamma x t1 ->
    variable_lookup Gamma x t2 ->
    t1 = t2.
Proof.
  intros Gamma x t1 t2 H1.
  induction H1; intros H2; inversion H2; subst; try contradiction; eauto.
Qed.

Lemma property_lookup_unique : forall Delta n sch1 sch2,
    property_lookup Delta n sch1 ->
    property_lookup Delta n sch2 ->
    sch1 = sch2.
Proof.
  intros.
  unfold property_lookup in *.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

Theorem unique_types : forall Gamma Delta e t1 t2,
    has_type Gamma Delta e t1 ->
    has_type Gamma Delta e t2 ->
    t1 = t2.
Proof.
  intros Gamma Delta e t1 t2 Htyp1 Htyp2.
  generalize dependent t2.
  induction Htyp1; intros t2' Htyp2; inversion Htyp2; subst; try reflexivity.
  -
    apply variable_lookup_unique with (t1 := sch0) in H.
    subst.
    eapply instantiate_unique'.
    + eassumption.
    + eassumption.
    + assumption.

  -
    apply property_lookup_unique with (sch1 := sch0) in H.
    subst.
    + eapply instantiate_unique'.
      * eassumption.
      * eassumption.
    + assumption.
  -
    apply IHHtyp1_1 in H3.
    inversion H3. subst.
    reflexivity.
  -
    apply IHHtyp1. assumption.
  -
    f_equal. apply IHHtyp1. assumption.
  -
    assert (Hinst1 : instantiate (Ty_Forall ts t1) (map Ty_Var ts) t1) by apply instantiate_id.
    assert (Hinst2 : instantiate (Ty_Forall ts t0) (map Ty_Var ts) t0) by apply instantiate_id.
    assert (Ht10 : t1 = t0).
    { eapply (H0 (map Ty_Var ts) t1 Hinst1).
      apply H8 with (ts_args := map Ty_Var ts). assumption. }
    subst t0.
    apply IHHtyp1 in H9.
    assumption.
  -
    apply IHHtyp1_2. assumption.
  -
    f_equal. apply IHHtyp1_1. assumption.
    apply IHHtyp1_2. assumption.
  -
    apply IHHtyp1 in H2.
    inversion H2. subst. reflexivity.
  -
    apply IHHtyp1 in H2.
    inversion H2. subst. reflexivity.
Qed.
