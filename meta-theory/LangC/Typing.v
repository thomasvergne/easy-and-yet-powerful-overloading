
Require Import Overloading.LangC.Definitions.
Require Import Overloading.LangC.Maps.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Lists.List.
From Stdlib Require PeanoNat.
Require Import Stdlib.Strings.String.
Import ListNotations.
Require Import Arith Lia.

Lemma canonical_form_tuple :
  forall e t1 t2,
    has_type empty [] e (Ty_Tuple t1 t2) ->
    value e ->
    exists e1 e2,
      e = E_Pair e1 e2.
Proof.
  intros e t1 t2 Htyp Hval.
  inversion Hval; subst; try (inversion Htyp; subst).
  exists e1, e2. reflexivity.
Qed.

Lemma weakening :
  forall Gamma Gamma' Delta e tau,
    includedin Gamma Gamma' ->
    has_type Gamma  Delta e tau ->
    has_type Gamma' Delta e tau.
Proof.
  intros Gamma Gamma' Delta e tau Hinc Htyp.

  generalize dependent Gamma'.

  induction Htyp; intros Gamma' Hinc.
  - constructor.
  - constructor.
  - constructor.
  - unfold includedin in Hinc.
    apply Hinc in H.
    apply T_Var; assumption.
  - apply IHHtyp in Hinc.
    constructor.
    assumption.
  - apply IHHtyp in Hinc.
    constructor.
    assumption.
  - apply T_Over with (t1 := t1).
    + apply IHHtyp. assumption.
    + assumption.

  - apply T_App with (t1 := t1).
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
  - apply T_Add; [apply IHHtyp1 | apply IHHtyp2];
      assumption.
  - apply T_Property.
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
  - apply T_Abs with (t2 := t2).
    apply IHHtyp. apply includedin_update. assumption.
  - apply T_Let with (t1 := t1) (t2 := t2).
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. apply includedin_update. assumption.
  - apply T_If with (t := t).
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
    + apply IHHtyp3. assumption.
  - apply T_Pair.
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
  - apply T_Fst with (t2 := t2).
    apply IHHtyp. assumption.
  - apply T_Snd with (t1 := t1).
    apply IHHtyp. assumption.
Qed.

Lemma weakening_empty :
  forall Gamma Delta e tau,
    has_type empty Delta e tau ->
    has_type Gamma Delta e tau.
Proof.
  intros. apply weakening with (Gamma := empty).
  - unfold includedin. intros.
    inversion H0.
  - assumption.
Qed.

Lemma canonical_form_arrow :
  forall e t1 t2,
    has_type empty [] e (Ty_Arrow t1 t2) ->
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
    has_type empty [] e Ty_Nat ->
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
    has_type empty [] e Ty_Bool ->
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

Definition extends (D1 D2: impls) :=
  forall n s, context_lookup D1 n s -> context_lookup D2 n s.

Lemma extends_refl : forall D, extends D D.
Proof.
  intros D n s H.
  assumption.
Qed.
(*
Lemma update_extends : forall D n sch,
  extends D (update_impls D n sch).
Proof.
  intros D n sch.
  unfold extends.
  intros n' T Hlookup.
  unfold update_impls.
  simpl.


Qed. *)

Lemma extends_cons : forall D D' n sch,
  extends D D' ->
  extends (update_impls D n sch) (update_impls D' n sch).
Proof.
  intros D D' n sch Hext n' s Hlookup.
  unfold update_impls in Hlookup |- *.
  inversion Hlookup; subst.
  - apply CL_Here. reflexivity.
  (* - apply CL_Diff.
    + assumption.
    + assumption.
    + apply Hext. assumption. *)
  - apply CL_There.
    + assumption.
    + apply Hext. assumption.
Qed.


Lemma weakening_Delta :
  forall Gamma Delta Delta' e tau,
    extends Delta Delta' ->
    has_type Gamma Delta e tau ->
    has_type Gamma Delta' e tau.
Proof.
  intros Gamma Delta Delta' e tau Hext Htyp.
  generalize dependent Delta'.
  induction Htyp; intros Delta' Hext.
  - constructor.
  - constructor.
  - constructor.
  - apply T_Var; assumption.
  - apply IHHtyp in Hext.
    constructor.
    assumption.
  - apply IHHtyp in Hext.
    constructor.
    assumption.
  - apply T_Over with (t1 := t1).
    + apply IHHtyp. assumption.
    + apply Hext. assumption.
  - apply T_App with (t1 := t1).
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
  - apply T_Add; [apply IHHtyp1 | apply IHHtyp2];
      assumption.
  - eapply T_Property.
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. unfold update_impls. apply extends_cons. assumption.
  - apply T_Abs with (t2 := t2).
    apply IHHtyp. assumption.
  - apply T_Let with (t1 := t1) (t2 := t2).
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
  - apply T_If with (t := t).
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
    + apply IHHtyp3. assumption.
  - apply T_Pair.
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
  - apply T_Fst with (t2 := t2).
    apply IHHtyp. assumption.
  - apply T_Snd with (t1 := t1).
    apply IHHtyp. assumption.
Qed.

Lemma typed_canonical_form_arrow :
  forall e t1 t2,
    has_type empty [] e (Ty_Arrow t1 t2) ->
    value e ->
    exists x t e1,
      e = E_Abs x t e1.
Proof.
  intros e t1 t2 Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists x, t1, e0. split; reflexivity.
Qed.

Lemma canonical_form_forall :
  forall e (sch: type),
    has_type empty [] e (Ty_Forall sch) ->
    value e ->
    exists e1,
      e = E_TypeAbs e1.
Proof.
  intros e sch Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists e0. reflexivity.
Qed.


Theorem progress :
  forall e t,
    has_type empty [] e t ->
    value e \/ (exists e', step e e').
Proof.
    intros e t Htyp.
    remember empty as Gamma.
    remember [] as Delta.

    induction Htyp; subst.
    - left. constructor.
    - left. constructor.
    - left. constructor.
    - inversion H.
    - (* E_TypeAbs *)
      left. constructor.
    - (* E_TypeApp *)
      destruct IHHtyp as [Hval | [e' Hstep]]; try reflexivity.
      + destruct (canonical_form_forall _ _ Htyp Hval) as [e1 Heq].
        subst. right. exists (apply_type_expr T2 e1).
        constructor.
      + right. exists (E_TypeApp e' T2). constructor. assumption.
    - inversion H; subst.
    - (* E_App *)
      right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
      + destruct IHHtyp2 as [Hval2 | [e2' Hstep2]]; try reflexivity.
        * destruct (canonical_form_arrow _ _ _ Htyp1 Hval1) as [x [t [body]]].
          subst. exists (subst_expr x e2 body). constructor. assumption.
        * exists (E_App e1 e2'). constructor. assumption.
          assumption.
      + exists (E_App e1' e2). constructor. assumption.
    - right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]];
        try reflexivity;
        destruct IHHtyp2 as [Hval2 | [e2' Hstep2]]; try reflexivity.
        * destruct (canonical_form_nat _ Htyp1 Hval1) as [n];
          destruct (canonical_form_nat _ Htyp2 Hval2) as [m].
          subst. exists (E_Const (n + m)). constructor.
        * exists (E_Add e1 e2'). constructor. assumption.
          assumption.
        * exists (E_Add e1' e2). constructor. assumption.
        * exists (E_Add e1' e2). constructor. assumption.
    - (* E_Property *)
      right. destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
      + exists (subst_over n e1 e2). constructor. assumption.
      + exists (E_Property n t e1' e2). constructor. assumption.
    - (* E_Abs *)
      left. constructor.
    - right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
      + exists (subst_expr x e1 e2). constructor. assumption.
      + exists (E_Let x e1' e2). constructor. assumption.
    - right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
      + destruct (canonical_form_bool _ Htyp1 Hval1) as [Heq | Heq]; subst.
        * exists e2. constructor.
        * exists e3. constructor.
      + exists (E_If e1' e2 e3). constructor. assumption.
  - destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
    + destruct IHHtyp2 as [Hval2 | [e2' Hstep2]]; try reflexivity.
      * left. constructor. assumption. assumption.
      * right. exists (E_Pair e1 e2'). constructor. assumption.
        assumption.
    + right. exists (E_Pair e1' e2). constructor. assumption.
  - destruct IHHtyp as [Hval | [e' Hstep]]; try reflexivity.
    + destruct (canonical_form_tuple _ _ _ Htyp Hval) as [e1 [e2 Heq]].
      subst. right. exists e1. constructor.
      inversion Hval; subst. assumption.
      inversion Hval; subst. assumption.
    + right. exists (E_Fst e'). constructor. assumption.
  - destruct IHHtyp as [Hval | [e' Hstep]]; try reflexivity.
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


Lemma substitution_preserves_typing : forall Delta Gamma x U e v T,
    has_type (x |-> U ; Gamma) Delta e T ->
    has_type empty [] v U ->
    has_type Gamma Delta (subst_expr x v e) T.
Proof.
  intros Delta Gamma x U e v T Htyp_e Htyp_v.
  generalize dependent Gamma.
  generalize dependent Delta.
  generalize dependent T.

  induction e; intros T Delta Gamma Htyp_e; simpl; inversion Htyp_e; subst.
  - (* E_Const *)
    constructor.
  - (* E_Bool *)
    constructor.
  - (* E_String *)
    constructor.
  - (* E_Var *)
    simpl.
    destruct (String.eqb_spec x0 x).
    + (* x0 = x *)
      subst.
      rewrite String.eqb_refl.
      rewrite update_eq in H2. injection H2 as Heq. subst.
      apply weakening_empty.
      apply weakening_Delta with (Delta := []).
      * unfold extends. intros name s0 Hlook.
        inversion Hlook; subst.
      * assumption.
    + (* x0 <> x *)
      apply neq_sym in n.
      rewrite update_neq in H2; try assumption.
      * rewrite eqb_false.
        apply T_Var.
        -- assumption.
        -- assumption.
      * symmetry. assumption.
  - (* E_App *)
    apply T_App with (t1 := t1).
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* E_Add *)
    apply T_Add; [apply IHe1 | apply IHe2]; assumption.
  - (* E_TypeAbs *)
    inversion Htyp_e; subst.
    apply T_TypeAbs.
    apply IHe. assumption.
  - (* E_TypeApp *)
    inversion Htyp_e; subst.
    apply T_TypeApp.
    apply IHe. assumption.
  - (* E_Property *)
    eapply T_Property.
    + apply IHe1; assumption.
    + apply IHe2; assumption.
    (* + assumption.
    + apply IHe1. assumption. assumption.
    + apply IHe2.
      * apply weakening_Delta with (Delta := Delta).
        -- unfold extends. intros name s Hlook.
           unfold update_impls. applyu
        -- assumption.
      * assumption. *)
  - apply T_Over with (t1 := t1).
    + apply IHe; assumption.
    + assumption.
  - (* E_Abs *)
    inversion Htyp_e; subst.
    apply T_Abs with (t2 := t2).
    simpl.
    destruct (String.eqb_spec x0 x).
    + (* x0 = x *)
      subst. rewrite eqb_refl.
      rewrite update_shadow in H2.
      assumption.
    + (* x0 <> x *)
      rewrite eqb_false; try assumption.
      apply IHe.
      * rewrite update_permute. assumption.
        assumption.
      * symmetry. assumption.
  - (* E_Let *)
    apply T_Let with (t1 := t1) (t2 := T).
    + apply IHe1; assumption.
    + simpl.
      destruct (String.eqb_spec x0 x).
      * (* x0 = x *)
        subst. rewrite eqb_refl.
        rewrite update_shadow in H6.
        assumption.
      * (* x0 <> x *)
        rewrite eqb_false; try assumption.
        apply IHe2.
        -- rewrite update_permute; try assumption.
        -- symmetry. assumption.
  - (* E_Pair *)
    apply T_Pair.
    + apply IHe1. assumption.
    + apply IHe2. assumption.

  - (* E_Fst *)
    apply T_Fst with (t2 := t2).
    apply IHe. assumption.

  - (* E_Snd *)
    apply T_Snd with (t1 := t1).
    apply IHe. assumption.
  - (* E_If *)
    apply T_If with (t := T).
    + apply IHe1; assumption.
    + apply IHe2; assumption.
    + apply IHe3; assumption.
Qed.

Lemma extends_mask : forall Delta n t sch,
  extends (update_impls (update_impls Delta n sch) n t) (update_impls Delta n t).
Proof.
  unfold update_impls. intros.
  unfold extends. intros x s Hlook.
  simpl in Hlook.
  inversion Hlook; subst.
  - apply CL_Here. reflexivity.
  (* - apply CL_Diff.
    + assumption.
    + assumption.
    + inversion H6; subst.
      * contradiction H2. reflexivity.
      * assumption.
      * assumption. *)
  - apply CL_There.
    + assumption.
    + inversion H5; subst.
      * contradiction H4. reflexivity.
      * assumption.
Qed.

Lemma extends_permute : forall Delta n1 sch1 n2 sch2,
  n1 <> n2 ->
  extends
    (update_impls (update_impls Delta n1 sch1) n2 sch2)
    (update_impls (update_impls Delta n2 sch2) n1 sch1).
Proof.
  unfold update_impls. intros Delta n1 sch1 n2 sch2 Hneq.
  unfold extends. intros x s Hlook.
  simpl in Hlook.
  inversion Hlook; subst.
  - apply CL_There.
    + symmetry. assumption.
    + apply CL_Here. reflexivity.
  (* - inversion H6; subst.
    + apply CL_Here. reflexivity.
    + apply CL_There.
      * assumption.
      * apply CL_There.
        -- assumption.
        -- assumption.
    + apply CL_There.
      * assumption.
      * apply CL_There.
        -- assumption.
        -- assumption. *)
  - inversion H5; subst.
    + apply CL_Here. reflexivity.
    + apply CL_There.
      * assumption.
      * apply CL_There.
        -- assumption.
        -- assumption.
    (* + apply CL_There.
      * assumption.
      * apply CL_There.
        -- assumption.
        -- assumption. *)
Qed.

(* has_type Gamma Delta
(if name =? n then v else E_Over (subst_over n v e) name) t2
(if name =? n
then tv
else TE_Over (subst_over_typed n tv te) name (Ty_Arrow t1
t2)) *)

(* Lemma folding_subst_over : forall Gamma Delta n name e v tv te t1 t2,
    has_type Gamma Delta
      (if name =? n then v else E_Over (subst_over n v e) name) t2
      (if name =? n then tv else TE_Over (subst_over_typed n tv te) name (Ty_Arrow t1 t2))
 ->
    has_type Gamma Delta (subst_over n v e) t2 (subst_over_typed n tv te).
Proof.
  intros.

Qed. *)

Lemma substitution_over_preserves_typing : forall Gamma Delta n e v t tbody,
    has_type Gamma (update_impls Delta n t) e tbody ->
    has_type empty [] v t ->
    has_type Gamma Delta (subst_over n v e) tbody.
Proof.
  intros Gamma Delta n e v t tbody H_type_e H_type_v.

  generalize dependent Gamma.
  generalize dependent Delta.
  generalize dependent tbody.

  induction e; intros tbody Delta Gamma H_type_e; simpl; inversion H_type_e; subst.
  - (* E_Const *)
    constructor.
  - (* E_Bool *)
    constructor.
  - (* E_String *)
    constructor.
  - (* E_Var *)
    apply T_Var; assumption.
  - (* E_App *)
    apply T_App with (t1 := t1).
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* E_Add *)
    apply T_Add; [apply IHe1 | apply IHe2]; assumption.
  - (* E_TypeAbs *)
    apply T_TypeAbs.
    simpl.
    apply IHe. assumption.
  - (* E_TypeApp *)
    apply T_TypeApp.
    apply IHe. assumption.
  - (* E_Property *)
    destruct (String.eqb_spec n0 n) as [Heq | Hneq].
    + subst n0.
      simpl.
      eapply T_Property.
      * apply IHe1. exact H6.
      * eapply weakening_Delta.
        -- apply extends_mask.
        -- exact H7.
    + simpl.
      eapply T_Property.
      * apply IHe1. exact H6.
      * eapply IHe2.
        -- eapply weakening_Delta.
         ++ apply extends_permute. apply neq_sym. exact Hneq.
           ++ exact H7.
  - (* E_Over *)
    destruct (String.eqb_spec n name) as [Heqname | Hneqname].
    + (* n = name *)
      subst name.
      rewrite String.eqb_refl.
      simpl.

      assert (Ht : t = Ty_Arrow t1 tbody).
      {
        inversion H_type_e; subst.
        inversion H5; subst.
        - reflexivity.
        - contradiction H8. reflexivity.
      }
      apply T_App with (t1 := t1).
      * apply weakening_empty.
        eapply weakening_Delta with (Delta := []).
        -- unfold extends. intros n' s Hlook. inversion Hlook.
        -- rewrite <- Ht. assumption.
      * apply IHe.
        exact H3.
    + (* n <> name *)
      rewrite eqb_false; try assumption.
      simpl.
      apply T_Over with (t1 := t1).
      -- apply IHe.
        exact H3.
      -- inversion H5; subst.
        * contradiction Hneqname. reflexivity.
        * assumption.
      -- symmetry. assumption.
  - simpl. constructor.
    apply IHe. assumption.
  - simpl. apply T_Let with (t1 := t1) (t2 := tbody).
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl. constructor.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl. apply T_Fst with (t2 := t2).
    apply IHe. assumption.
  - simpl. apply T_Snd with (t1 := t1).
    apply IHe. assumption.
  - simpl. apply T_If.
    + apply IHe1. assumption.
    + apply IHe2. assumption.
    + apply IHe3. assumption.
Qed.

Lemma context_lookup_apply_type : forall Delta repl n T,
    context_lookup Delta n T ->
    context_lookup
      (apply_type_env_impls repl Delta)
      n
      (apply_type repl T).
Proof.
  intros Delta repl n T H.
  induction H; simpl.
  - apply CL_Here. subst. reflexivity.
  - apply CL_There; assumption.
Qed.

Lemma apply_type_env_lookup : forall Gamma x t repl,
  Gamma x = Some t ->
  (apply_type_env repl Gamma) x = Some (apply_type repl t).
Proof.
  intros Gamma x t repl H.
  unfold apply_type_env.
  rewrite H. reflexivity.
Qed.

Lemma apply_type_env_update : forall (Gamma : partial_map type) x t (repl : type),
   apply_type_env repl (x |-> t; Gamma) =
  (x |-> (apply_type repl t); (apply_type_env repl Gamma)).
Proof.
  intros Gamma x t repl.
  unfold apply_type_env, update.
  apply FunctionalExtensionality.functional_extensionality. intros y.
  destruct (String.eqb x y) eqn:Heq.
  - apply String.eqb_eq in Heq. subst.
    repeat rewrite t_update_eq.
    reflexivity.
  - apply String.eqb_neq in Heq.
    repeat rewrite t_update_neq by (intro Hxy; apply Heq; symmetry; exact Hxy).
    reflexivity.
Qed.

Lemma apply_type_env_impls_update : forall Delta n sch repl,
  apply_type_env_impls repl (update_impls Delta n sch) =
  update_impls (apply_type_env_impls repl Delta) n (apply_type repl sch).
Proof.
  intros Delta n sch repl.
  unfold update_impls. simpl. reflexivity.
Qed.

Lemma succ_eq_plus_one : forall n, S n = n + 1.
Proof.
  intros n. induction n; simpl.
  - reflexivity.
  - rewrite <- IHn. reflexivity.
Qed.

Lemma type_shift_S_k_gen : forall k c repl,
  type_shift (S k) c repl = type_shift 1 c (type_shift k c repl).
Proof.
  intros k c repl.
  generalize dependent c.
  induction repl; intros c; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHrepl1, IHrepl2. reflexivity.
  - destruct (Nat.leb c v) eqn:Hcv.
    + apply PeanoNat.Nat.leb_le in Hcv.
      destruct (Nat.leb c (v + k)) eqn:Hcvk.
      * cbn.
        rewrite Hcvk.
        repeat rewrite PeanoNat.Nat.add_succ_r.
        auto.
      * apply PeanoNat.Nat.leb_gt in Hcvk.
        exfalso.
        apply (PeanoNat.Nat.lt_irrefl (v + k)).
        eapply PeanoNat.Nat.lt_le_trans.
        -- exact Hcvk.
        -- eapply PeanoNat.Nat.le_trans; [exact Hcv | apply PeanoNat.Nat.le_add_r].
    + apply PeanoNat.Nat.leb_gt in Hcv.
      destruct (Nat.leb c v) eqn:E.
      * apply PeanoNat.Nat.leb_le in E.
        exfalso.
        apply (PeanoNat.Nat.lt_irrefl v).
        eapply PeanoNat.Nat.lt_le_trans.
        -- exact Hcv.
        -- exact E.
      * cbn.
        rewrite E.
        reflexivity.
  - f_equal. eauto.
  - rewrite IHrepl1, IHrepl2. reflexivity.
Qed.

Lemma apply_type_shift_depth : forall T repl k,
  apply_type (type_shift (S k) 0 repl) T =
  apply_type (type_shift 1 0 (type_shift k 0 repl)) T.
Proof.
  intros T repl k.
  rewrite type_shift_S_k_gen.
  reflexivity.
Qed.

Lemma lt_0_false : forall n,
  n < 0 -> False.
Proof.
  intros.
  lia.
Qed.

Lemma if_same : forall A (b: bool) (x : A),
  (if b then x else x) = x.
Proof.
  intros.
  induction b. simpl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma type_shift_S_k : forall k repl,
  type_shift (S k) 0 repl = type_shift 1 0 (type_shift k 0 repl).
Proof.
  intros k repl.
  apply type_shift_S_k_gen.
Qed.

Lemma type_shift_shifted_comm : forall d c repl,
  type_shift d (S c) (type_shift 1 0 repl) =
  type_shift 1 0 (type_shift d c repl).
Proof.
  intros d c repl.
  induction repl; simpl; try reflexivity.
  - rewrite IHrepl1, IHrepl2. reflexivity.
  - simpl.
    destruct (Nat.leb c v) eqn:Hcv.
    + apply PeanoNat.Nat.leb_le in Hcv.
      assert (H: v + 1 + d = v + d + 1).
        {
          rewrite Nat.add_comm. rewrite Nat.add_assoc.
          rewrite Nat.add_comm.
          assert (H' : d + v = v + d).
          {
            rewrite Nat.add_comm. auto.
          }
          rewrite H'. rewrite Nat.add_comm. reflexivity.
        }
      destruct (Nat.leb (S c) (S v)) eqn:Hc2; simpl; try lia.
      apply PeanoNat.Nat.leb_le in Hc2.
      * rewrite <- succ_eq_plus_one.
        apply Nat.leb_le in Hcv.
        rewrite Hcv.
        rewrite succ_eq_plus_one.
        rewrite H. reflexivity.
      * rewrite <- succ_eq_plus_one.
        apply Nat.leb_le in Hcv.
        rewrite Hcv. rewrite succ_eq_plus_one.
        rewrite H. auto.
    + rewrite <- succ_eq_plus_one.
      rewrite Hcv. simpl.
      rewrite succ_eq_plus_one.
      auto.
  - f_equal.

Qed.

Search (forall n, (n + 0) = n).

(* Shifter puis substituer = substituer (avec repl shifté) puis shifter *)
Lemma type_shift_apply_type : forall T repl d c,
  type_shift d c (apply_type repl T) =
  apply_type (type_shift d c repl) (type_shift d (S c) T).
Proof.
  induction T; intros repl d c; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - (* Ty_Var v *)
    destruct v; simpl.
    + (* v = 0 : on substitue *)
      destruct (Nat.leb c 0) eqn:Hle.
      * apply PeanoNat.Nat.leb_le in Hle.
        assert (c = 0).
        { apply PeanoNat.Nat.le_lteq in Hle. destruct Hle.
          - apply lt_0_false in H. exfalso. exact H.
          - assumption.
        }
        subst. simpl. reflexivity.
      * reflexivity.
    + (* v = S v' *)
      simpl.
      destruct (Nat.leb c (S v)) eqn:Hle;
      destruct (Nat.leb (S c) (S v)) eqn:Hle2;
      simpl; try reflexivity;
      apply Nat.leb_le in Hle + Hle2 ||
      apply Nat.leb_gt in Hle + Hle2; try lia.
      * destruct (Nat.leb c (S v + d)) eqn:Hle3.
        -- simpl in *. rewrite Hle2. simpl. reflexivity.
        -- apply Nat.leb_gt in Hle3. lia.
      * destruct (Nat.leb c (S v)) eqn:Hle3.
        -- simpl in *. rewrite Hle2. simpl. reflexivity.
        -- simpl in *. rewrite Hle2. simpl. reflexivity.
      * simpl in *. rewrite Hle2. simpl. reflexivity.
      * simpl in *. rewrite Hle2. simpl. reflexivity.
  - simpl.
    f_equal.
    rewrite IHT with (repl := type_shift 1 0 repl).
    apply type_shift_shifted_comm.
Qed.

Lemma type_substitution_preserves_typing : forall e T Gamma Delta repl,
    has_type Gamma Delta e T ->
    has_type (apply_type_env repl Gamma)
             (apply_type_env_impls repl Delta)
             (apply_type_expr repl e)
             (apply_type repl T).
Proof.
  intros e T Gamma Delta repl Htyp.
  generalize dependent repl.
  induction Htyp; intros repl; simpl.
  - constructor.
  - constructor.
  - constructor.
  - apply T_Var.
    apply apply_type_env_lookup.
    assumption.
  - constructor.

Qed.

Theorem preservation :
  forall e e' t,
    has_type empty [] e t ->
    step e e' ->
    has_type empty [] e' t.
Proof.
  intros e e' t Htyp Hstep.
  generalize dependent t.

  induction Hstep; intros t' Htyp.

  - (* ST_AppAbs : (λx:T.e) v → [x:=v]e *)
    inversion Htyp; subst.
    inversion H4; subst.
    eapply substitution_preserves_typing; eassumption.

  - (* ST_App1 : e1 → e1' ⇒ e1 e2 → e1' e2 *)
    inversion Htyp; subst.
    eapply T_App.
    + eapply IHHstep. eassumption.
    + assumption.

  - (* ST_App2 : e2 → e2' ⇒ v1 e2 → v1 e2' *)
    inversion Htyp; subst.
    eapply T_App.
    + eassumption.
    + apply IHHstep. assumption.

  - (* ST_AddConstConst : n1 + n2 → (n1+n2) *)
    inversion Htyp; subst.
    constructor.

  - (* ST_Add1 : e1 → e1' ⇒ e1 + e2 → e1' + e2 *)
    inversion Htyp; subst.
    econstructor.
    eapply IHHstep. eassumption.
    assumption.

  - (* ST_Add2 : e2 → e2' ⇒ v1 + e2 → v1 + e2' *)
    inversion Htyp; subst.
    econstructor.
    assumption.
    eapply IHHstep. eassumption.

  - (* ST_PropertyStep *)
    inversion Htyp; subst.
    econstructor.
    eapply IHHstep. eassumption.
    assumption.

  - (* ST_TypeAppStep *)
    inversion Htyp; subst.
    constructor.
    apply IHHstep. assumption.

  - (* ST_TypeAppAbs *)
    inversion Htyp; subst.
    inversion H4; subst.
    apply type_substitution_preserves_typing.
    assumption.


  - (* ST_PropertySubst *)
    inversion Htyp; subst.
    eapply substitution_over_preserves_typing; eassumption.

  - (* ST_Let : e1 → e1' ⇒ let x = e1 in e2 → let x = e1' in e2 *)
    inversion Htyp; subst.
    econstructor.
    + eapply IHHstep. eassumption.
    + assumption.

  - (* ST_Let_V : let x = v in e2 → [x:=v]e2 *)
    inversion Htyp; subst.
    eapply substitution_preserves_typing; eassumption.

  - (* ST_IfTrue : if true then e2 else e3 → e2 *)
    inversion Htyp; subst.
    assumption.

  - (* ST_IfFalse : if false then e2 else e3 → e3 *)
    inversion Htyp; subst.
    assumption.

  - (* ST_If : e1 → e1' ⇒ if e1 then e2 else e3 → if e1' then e2 else e3 *)
    inversion Htyp; subst.
    eauto.

  - (* ST_Pair1 : e1 → e1' ⇒ (e1, e2) → (e1', e2) *)
    inversion Htyp; subst.
    eauto.

  - (* ST_Pair2 : e2 → e2' ⇒ (v1, e2) → (v1, e2') *)
    inversion Htyp; subst.
    eauto.

  - (* ST_FstPair : fst (v1, v2) → v1 *)
    inversion Htyp; subst.
    inversion H4; subst.
    assumption.

  - (* ST_Fst : e → e' ⇒ fst e → fst e' *)
    inversion Htyp; subst.
    eauto.

  - (* ST_SndPair : snd (v1, v2) → v2 *)
    inversion Htyp; subst.
    inversion H4; subst.
    assumption.

  - (* ST_Snd : e → e' ⇒ snd e → snd e' *)
    inversion Htyp; subst.
    eauto.
Admitted.


Definition stuck (t: expr) : Prop :=
  (normal_form step) t /\ not (value t).

Theorem soundness :
  forall e e' t,
    has_type empty [] e t ->
    (multistep e e') ->
    not (stuck e').
Proof.
  intros e e' t Htyp Hmulti.

  induction Hmulti.
  - (* multi_refl *)
    intros [Hnf Hnotval].
    apply Hnotval.
    apply progress in Htyp.
    destruct Htyp as [Hval | [e' Hstep]].
    + assumption.
    + exfalso. apply Hnf. exists e'. assumption.
  - (* multi_step *)
    intros [Hnf Hnotval].
    apply IHHmulti.
    + eapply preservation.
      * exact Htyp.
      * assumption.
    + unfold stuck. split; assumption.
Qed.

Lemma gamma_eq_impl_typ_eq :
  forall (Gamma : context) x sch1 sch2,
    Gamma x = Some sch1 ->
    Gamma x = Some sch2 ->
    sch1 = sch2.
Proof.
  intros. rewrite H in H0. inversion H0.
  reflexivity.
Qed.

Lemma context_lookup_eq : forall Delta n sch1 sch2,
    sch1 = sch2 ->
    context_lookup Delta n sch1 ->
    context_lookup Delta n sch2.
Proof.
  intros Delta n sch1 sch2 Hsch Hlookup.
  rewrite Hsch in Hlookup. assumption.
Qed.

Lemma context_lookup_unique : forall Delta n sch1 sch2,
    context_lookup Delta n sch1 ->
    context_lookup Delta n sch2 ->
    sch1 = sch2.
Proof.
  intros Delta n sch1 sch2 H1.
  induction H1; intros H2; inversion H2; subst; try contradiction; eauto.
Qed.

Theorem unique_types : forall Gamma Delta e t1 t2,
    has_type Gamma Delta e t1 ->
    has_type Gamma Delta e t2 ->
    t1 = t2.
Proof.
  intros Gamma Delta e t1 t2 Htyp1 Htyp2.
  generalize dependent t2.
  induction Htyp1; intros t2' Htyp2; inversion Htyp2; subst; try reflexivity.
  - (* T_Var *)
    eapply gamma_eq_impl_typ_eq in H.
    symmetry. eassumption.
    assumption.
  - (* T_TypeAbs *)
    apply IHHtyp1 in H2. subst. reflexivity.
  - (* T_TypeApp *)
    apply IHHtyp1 in H4. subst. injection H4 as Heq. subst. reflexivity.
  - (* T_Over *)
    apply IHHtyp1 in H4.
    subst t0.
    assert (Heq : Ty_Arrow t1 t2 = Ty_Arrow t1 t2').
    { eapply context_lookup_unique; eauto. }
    inversion Heq. reflexivity.
  - (* T_App *)
    apply IHHtyp1_1 in H3.
    inversion H3. subst.
    reflexivity.
  - (* T_Property *)
    apply IHHtyp1_2. assumption.
  - (* T_Abs *)
    f_equal. apply IHHtyp1. assumption.
  - (* T_Let *)
    apply IHHtyp1_1 in H5. subst. apply IHHtyp1_2. assumption.
  - (* T_If *)
    apply IHHtyp1_2. assumption.
  - (* T_Pair *)
    f_equal. apply IHHtyp1_1. assumption.
    apply IHHtyp1_2. assumption.
  - (* T_Fst *)
    apply IHHtyp1 in H2.
    inversion H2. subst. reflexivity.
  - (* T_Snd *)
    apply IHHtyp1 in H2.
    inversion H2. subst. reflexivity.
Qed.
