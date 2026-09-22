Require Import Overloading.LangB.Definitions.
Require Import Overloading.LangB.Maps.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.String.
Import ListNotations.

Lemma canonical_form_tuple :
  forall e t1 t2 te,
    has_type empty [] e (Ty_Tuple t1 t2) te ->
    value e ->
    exists e1 e2,
      e = E_Pair e1 e2.
Proof.
  intros e t1 t2 te Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists e1, e2. reflexivity.
Qed.

Lemma weakening :
  forall Gamma Gamma' Delta e tau te,
    includedin Gamma Gamma' ->
    has_type Gamma  Delta e tau te ->
    has_type Gamma' Delta e tau te.
Proof.
  intros Gamma Gamma' Delta e tau te Hinc Htyp.

  generalize dependent Gamma'.

  induction Htyp; intros Gamma' Hinc.
  - constructor.
  - constructor.
  - constructor.
  - apply T_Var.
    unfold includedin in Hinc.
    apply Hinc. assumption.
  - apply T_App with (t1 := t1).
    + apply IHHtyp1. assumption.
    + apply IHHtyp2. assumption.
  - apply T_Add; [apply IHHtyp1 | apply IHHtyp2];
      assumption.
  - apply T_Show with (t := t).
    assumption.
    apply IHHtyp. assumption.
  - apply T_LetShow with (t := t) (e := e).
    apply IHHtyp. assumption.
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
  forall Gamma Delta e tau te,
    has_type empty Delta e tau te ->
    has_type Gamma Delta e tau te.
Proof.
  intros. apply weakening with (Gamma := empty).
  - unfold includedin. intros.
    inversion H0.
  - assumption.
Qed.

Lemma canonical_form_arrow :
  forall e t1 t2 te,
    has_type empty [] e (Ty_Arrow t1 t2) te ->
    value e ->
    exists x t e1,
      e = E_Abs x t e1.
Proof.
  intros e t1 t2 te Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists x, t1, e0. reflexivity.
Qed.

Lemma canonical_form_nat :
  forall e te,
    has_type empty [] e Ty_Nat te ->
    value e ->
    exists n,
      e = E_Const n.
Proof.
  intros e te Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists n. reflexivity.
Qed.

Lemma canonical_form_bool :
  forall e te,
    has_type empty [] e Ty_Bool te ->
    value e ->
      (e = E_Bool true) \/ (e = E_Bool false).
Proof.
  intros e te HT HVal.
  destruct HVal; auto; try (inversion HT).
  inversion HT; subst.
  destruct b.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma typed_canonical_form_arrow :
  forall e t1 t2 te,
    has_type empty [] e (Ty_Arrow t1 t2) te ->
    value e ->
    exists x t e1 te1,
      e = E_Abs x t e1 /\ te = TE_Abs x t1 t2 te1.
Proof.
  intros e t1 t2 te Htyp Hval.
  inversion Hval; subst; try (inversion Htyp).
  exists x, t1, e0, te0. split; reflexivity.
Qed.

Theorem progress :
  forall e t te,
    has_type empty [] e t te ->
    value e \/ (exists e', step e e').
Proof.
    intros e t te Htyp.
    remember empty as Gamma.
    remember [] as Delta.

    induction Htyp; subst.
    - left. constructor.
    - left. constructor.
    - left. constructor.
    - inversion H.
    - (* E_App *)
      right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
      + destruct IHHtyp2 as [Hval2 | [e2' Hstep2]]; try reflexivity.
        * destruct (canonical_form_arrow _ _ _ _ Htyp1 Hval1) as [x [t [body]]].
          subst. exists (subst_expr x e2 body). constructor. assumption.
        * exists (E_App e1 e2'). constructor. assumption.
          assumption.
      + exists (E_App e1' e2). constructor. assumption.
    - right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]];
        try reflexivity;
        destruct IHHtyp2 as [Hval2 | [e2' Hstep2]]; try reflexivity.
        * destruct (canonical_form_nat _ _ Htyp1 Hval1) as [n];
          destruct (canonical_form_nat _ _ Htyp2 Hval2) as [m].
          subst. exists (E_Const (n + m)). constructor.
        * exists (E_Add e1 e2'). constructor. assumption.
          assumption.
        * exists (E_Add e1' e2). constructor. assumption.
        * exists (E_Add e1' e2). constructor. assumption.
    - inversion H.
    - inversion HeqDelta.
    - left. constructor.
    - right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
      + exists (subst_expr x e1 e2). constructor. assumption.
      + exists (E_Let x e1' e2). constructor. assumption.
    - right.
      destruct IHHtyp1 as [Hval1 | [e1' Hstep1]]; try reflexivity.
      + destruct (canonical_form_bool _ _ Htyp1 Hval1) as [Heq | Heq]; subst.
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
    + destruct (canonical_form_tuple _ _ _ _ Htyp Hval) as [e1 [e2 Heq]].
      subst. right. exists e1. constructor.
      inversion Hval; subst. assumption.
      inversion Hval; subst. assumption.
    + right. exists (E_Fst e'). constructor. assumption.
  - destruct IHHtyp as [Hval | [e' Hstep]]; try reflexivity.
    + destruct (canonical_form_tuple _ _ _ _ Htyp Hval) as [e1 [e2 Heq]].
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


Lemma substitution_preserves_typing : forall Gamma x U e v tv T te,
    has_type (x |-> U ; Gamma) [] e T te ->
    has_type empty [] v U tv ->
    has_type Gamma [] (subst_expr x v e) T (subst_typed_expr x tv te).
Proof.
  intros Gamma x U e v tv T te Htyp_e Htyp_v.
  generalize dependent Gamma.
  generalize dependent T.
  generalize dependent te.

  induction e; intros te T Gamma Htyp_e; simpl; inversion Htyp_e; subst.
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
      apply weakening_empty. assumption.
    + (* x0 <> x *)
      apply neq_sym in n.
      rewrite update_neq in H2; try assumption.
      * rewrite eqb_false.
        apply T_Var. assumption.
        assumption.
      * symmetry. assumption.
  - (* E_App *)
    apply T_App with (t1 := t1).
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* E_Add *)
    apply T_Add; [apply IHe1 | apply IHe2]; assumption.
  - (* E_Show *)
    apply T_Show with (t := t).
    assumption.
    apply IHe; assumption.
  - (* E_Abs *)
    apply T_Abs with (t2 := t2).
    simpl.
    destruct (String.eqb_spec x0 x).
    + (* x0 = x *)
      subst. rewrite eqb_refl.
      rewrite update_shadow in H6.
      assumption.
    + (* x0 <> x *)
      rewrite eqb_false; try assumption.
      apply IHe. rewrite update_permute; try assumption.
      symmetry. assumption.
  - (* E_Let *)
    apply T_Let with (t1 := t1) (t2 := T).
    + apply IHe1; assumption.
    + simpl.
      destruct (String.eqb_spec x0 x).
      * (* x0 = x *)
        subst. rewrite eqb_refl.
        rewrite update_shadow in H7.
        assumption.
      * (* x0 <> x *)
        rewrite eqb_false; try assumption.
        apply IHe2. rewrite update_permute; try assumption.
        symmetry. assumption.

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

Theorem preservation :
  forall e e' t te,
    has_type empty [] e t te ->
    step e e' ->
    exists te',
      has_type empty [] e' t te'.
Proof.
  intros e e' t te Htyp Hstep.
  generalize dependent te.
  generalize dependent t.

  induction Hstep; intros t' te Htyp.

  - (* ST_AppAbs : (λx:T.e) v → [x:=v]e *)
    inversion Htyp; subst.
    inversion H4; subst.
    exists (subst_typed_expr x te2 te).
    eapply substitution_preserves_typing; eassumption.

  - (* ST_App1 : e1 → e1' ⇒ e1 e2 → e1' e2 *)
    inversion Htyp; subst.
    edestruct IHHstep as [te1' Htyp1']; eauto.

  - (* ST_App2 : e2 → e2' ⇒ v1 e2 → v1 e2' *)
    inversion Htyp; subst.
    edestruct IHHstep as [te2' Htyp2']; eauto.

  - (* ST_AddConstConst : n1 + n2 → (n1+n2) *)
    inversion Htyp; subst.
    exists (TE_Const (n1 + n2)).
    constructor.

  - (* ST_Add1 : e1 → e1' ⇒ e1 + e2 → e1' + e2 *)
    inversion Htyp; subst.
    edestruct IHHstep as [te1' Htyp1']; eauto.

  - (* ST_Add2 : e2 → e2' ⇒ v1 + e2 → v1 + e2' *)
    inversion Htyp; subst.
    edestruct IHHstep as [te2' Htyp2']; eauto.

  - (* ST_Show : e → e' ⇒ show e → show e' *)
    inversion Htyp; subst.
    edestruct IHHstep as [te' Htyp']; eauto.

  - (* ST_LetShow : letShow x = show v in e → [x:=v]e *)
    inversion Htyp; subst.

  - (* ST_LetShow_Eval : e → e' ⇒ letShow x = e in e2 → letShow x = e' in e2 *)
    inversion Htyp; subst.

  - (* ST_Let : e1 → e1' ⇒ let x = e1 in e2 → let x = e1' in e2 *)
    inversion Htyp; subst.
    edestruct IHHstep as [te1' Htyp1']; eauto.

  - (* ST_Let_V : let x = v in e2 → [x:=v]e2 *)
    inversion Htyp; subst.
    exists (subst_typed_expr x te1 te2).
    eapply substitution_preserves_typing; eassumption.

  - (* ST_IfTrue : if true then e2 else e3 → e2 *)
    inversion Htyp; subst.
    exists te2.
    assumption.

  - (* ST_IfFalse : if false then e2 else e3 → e3 *)
    inversion Htyp; subst.
    exists te3.
    assumption.

  - (* ST_If : e1 → e1' ⇒ if e1 then e2 else e3 → if e1' then e2 else e3 *)
    inversion Htyp; subst.
    edestruct IHHstep as [te1' Htyp1']; eauto.

  - (* ST_Pair1 : e1 → e1' ⇒ (e1, e2) → (e1', e2) *)
    inversion Htyp; subst.
    edestruct IHHstep as [te1' Htyp1']; eauto.

  - (* ST_Pair2 : e2 → e2' ⇒ (v1, e2) → (v1, e2') *)
    inversion Htyp; subst.
    edestruct IHHstep as [te2' Htyp2']; eauto.

  - (* ST_FstPair : fst (v1, v2) → v1 *)
    inversion Htyp; subst.
    inversion H4; subst.
    exists te1. assumption.

  - (* ST_Fst : e → e' ⇒ fst e → fst e' *)
    inversion Htyp; subst.
    edestruct IHHstep as [te' Htyp']; eauto.

  - (* ST_SndPair : snd (v1, v2) → v2 *)
    inversion Htyp; subst.
    inversion H4; subst.
    exists te2. assumption.

  - (* ST_Snd : e → e' ⇒ snd e → snd e' *)
    inversion Htyp; subst.
    edestruct IHHstep as [te' Htyp']; eauto.
Qed.


Definition stuck (t: expr) : Prop :=
  (normal_form step) t /\ not (value t).

Theorem soundness :
  forall e e' t te,
    has_type empty [] e t te ->
    (multistep e e') ->
    not (stuck e').
Proof.
  intros e e' t te Htyp Hmulti.

  generalize dependent te.

  induction Hmulti.
  - (* multi_refl *)
    intros te Htyp [Hnf Hnotval].
    apply Hnotval.
    apply progress in Htyp.
    destruct Htyp as [Hval | [e' Hstep]].
    + assumption.
    + exfalso. apply Hnf. exists e'. assumption.
  - (* multi_step *)
    intros te Htyp [Hnf Hnotval].
    destruct (preservation x y t te Htyp H) as [te' Htyp'].
    apply IHHmulti with (te := te') in Htyp'.
    apply Htyp'. exact (conj Hnf Hnotval).
Qed.


