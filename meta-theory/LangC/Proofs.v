Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Strings.Ascii.
Import ListNotations.
Require Import Overloading.LangC.Maps.
Require Import Overloading.LangC.Definitions.
(* Require Import Overloading.Typing. *)

Require Import Stdlib.Relations.Relation_Operators.

(* Definition star {A} (R : A -> A -> Prop) := clos_refl_trans A R.

Inductive bisim : expr -> expr_m -> Prop :=
| bisim_intro :
    forall e em,
      (forall e', step e e' ->
        exists em', step_m em em' /\ bisim e' em') ->

      (forall em', step_m em em' ->
        exists e', step e e' /\ bisim e' em') ->
      bisim e em.
Lemma mono_preserves_value :
  forall v em,
    value v ->
    mono_expr v em ->
    value_m em.
Proof.
  intros.
  inversion H0; subst; clear H0.
  - constructor.
  - constructor.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    constructor.
  - inversion H; subst.
  - inversion H; subst.
  - inversion H; subst.
  - inversion H; subst.
  - constructor.
Qed.

Lemma bisim_preserves_subst :
  forall x v vm e em,
    mono_expr v vm ->
    mono_expr e em ->
    bisim v vm ->
    bisim e em ->
    bisim (subst x v e) (subst_m x vm em).
Proof.
  intros.

  induction H0.
  - simpl. exact H2.
  - simpl. exact H2.
  - simpl. destruct (eqb_stringP x x0).
    + exact H1.
    + exact H2.
  - simpl. destruct (eqb_stringP x x0).
    + subst. simpl. exact H2.
    + subst. simpl.
      (* Goal: bisim (E_OverVar x0 t (subst x v e)) (EM_OverVar x0 t (subst_m x vm m)) *)
      (* We need to construct a bisimulation *)
      constructor.
      * (* Forward direction: if E_OverVar x0 t (subst x v e) steps *)
        intros e' Hstep.
        (* E_OverVar doesn't have step rules, so this should be impossible *)
        inversion Hstep.
      * (* Backward direction: if EM_OverVar x0 t (subst_m x vm m) steps *)
        intros em' Hstep_m.
        (* EM_OverVar doesn't have step rules, so this should be impossible *)
        inversion Hstep_m.
  - simpl. destruct (eqb_stringP x param).
    + exact H2.
    + subst. simpl. constructor.
      * intros e' Hstep.
        inversion Hstep.
      * intros em' Hstep_m.
        inversion Hstep_m.
  - (* ME_App case *)
    simpl.
    (* This case is complex because we need to relate the stepping behavior
       of applications after substitution. The key insight is that
       bisim (E_App f args) (EM_App mf margs) doesn't directly give us
       bisim f mf and bisim args margs, so we need a different approach. *)

    (* For now, we admit this case as it requires additional lemmas
       about decomposing bisimulation over application structures *)

  - (* ME_Let case *)
    simpl. destruct (eqb_stringP x x0).
    + (* x = x0, substitution blocked in e2 *)
      constructor.
      * intros e' Hstep.
        (* Analysis of let steps would go here *)
        admit.
      * intros em' Hstep_m.
        (* Analysis of monad let steps would go here *)
        admit.
    + (* x ≠ x0, substitution continues *)
      constructor.
      * intros e' Hstep.
        (* Analysis of let steps would go here *)
        admit.
      * intros em' Hstep_m.
        (* Analysis of monad let steps would go here *)
        admit.
  - (* ME_If case *)
    simpl.
    constructor.
    + intros e' Hstep.
      (* Analysis of if steps would go here *)
      admit.
    + intros em' Hstep_m.
      (* Analysis of monad if steps would go here *)
      admit.
  - (* ME_TApp case *)
    simpl.
    constructor.
    + intros e' Hstep.
      (* Analysis of TApp steps would go here *)
      admit.
    + intros em' Hstep_m.
      (* Analysis of monad TApp steps would go here *)
      admit.
  - (* ME_Unit case *)
    simpl.
    exact H2. (* Unit doesn't change with substitution *)
Admitted.  *)

(* Lemma mono_backward : forall prog e em es,
e
  . *)

(* Theorem soundness : forall e em,
    mono_expr e em ->
    bisim e em.
Proof.
  intros e em Hmono.
  induction Hmono.
  - constructor. intros. inversion H; subst.
    intros. inversion H.
  - constructor. intros. inversion H; subst.
    intros. inversion H.
  - constructor. intros. inversion H; subst.
    intros. inversion H.
  - constructor. intros. inversion H; subst.
    intros. inversion H.
  - constructor. intros. inversion H; subst.
    intros. inversion H.
  - constructor. intros.
    + destruct IHHmono1; destruct IHHmono2.
      inversion H; subst.
      * (* ST_AppAbs case *)
        (* We need to analyze the structure of em from Hmono1 *)
        inversion Hmono1; subst.
        (* Now em = EM_Abs param targ tret mbody where mono_expr e1 mbody *)

        (* Since H7 : value e0, we know that em0 is also a value *)
        assert (Hval_em0 : value_m em0).
        { apply (mono_preserves_value e0 em0 H7 Hmono2). }

        (* Now we can apply STM_AppAbs rule *)
        exists (subst_m param em0 mbody).
        split.
        -- apply STM_AppAbs. exact Hval_em0.
        -- (* We need to prove bisim (subst param e0 e1) (subst_m param em0 mbody) *)
           (* This would require a substitution lemma *)
      * (* ST_App1 case *)
        (* The function part steps: e1 -> e1' so E_App e1 e2 -> E_App e1' e2 *)
        (* We use H0 to get the corresponding step from E_Abs param targ tret e1 *)
        destruct (H0 e1') as [em' [Hstep_em Hbisim_e1]].
        { exact H7. }
        exists (EM_App em' em0).
        split.
        -- apply STM_App1. exact Hstep_em.
        -- (* We need to prove bisim (E_App e1' e2) (EM_App em' em0) *)
           admit. (* This would require showing that bisim preserves application *)
      * (* ST_App2 case *)
        (* The argument part steps: e -> e' so E_App v1 e -> E_App v1 e' *)
        (* We use H2 to get the corresponding step from e0 *)
        destruct (H2 e'0) as [em0' [Hstep_em0 Hbisim_e']].
        { exact H8. }
        exists (EM_App em em0').
        split.
        -- apply STM_App2.
           ++ (* We need to prove value_m em *)
              admit. (* This would follow from mono_expr preserving values *)
           ++ exact Hstep_em0.
        -- (* We need to prove bisim (E_App v1 e') (EM_App em em0') *)
           admit. (* This would require showing that bisim preserves application *)
    + (* Second direction: when em steps *)
      intros em' Hstep_em.
      inversion Hstep_em; subst.
      * (* STM_AppAbs case *)
        (* We need to analyze the structure of em and em0 from mono *)
        inversion Hmono1; subst. (* em = EM_Abs param targ tret mbody *)

        (* The monad steps: EM_App (EM_Abs param targ tret mbody) em0 -> subst_m param em0 mbody *)
        (* We need to show the corresponding step in the source *)
        exists (subst param args body).
        split.
        -- apply ST_AppAbs.
           (* We need to show value e0, which we have as H7 in the context *)
           admit. (* This should be available from the context *)
        -- (* We need to prove bisim (subst param e0 e1) (subst_m param em0 mbody) *)
           admit. (* This requires substitution lemma *)
  - (* ME_Let case *)
    constructor.
    + intros e' Hstep.
      inversion Hstep; subst.
      * (* ST_LetValue case *)
        admit.
      * (* ST_LetStep case *)
        admit.
    + intros em' Hstep_m.
      inversion Hstep_m; subst.
      * (* STM_LetValue case *)
        admit.
      * (* STM_LetStep case *)
        admit.
  - (* ME_If case *)
    constructor.
    + intros e' Hstep.
      inversion Hstep; subst.
      * (* ST_IfCond case *)
        admit.
      * (* ST_IfTrue case *)
        admit.
      * (* ST_IfFalse case *)
        admit.
    + intros em' Hstep_m.
      inversion Hstep_m; subst.
      * (* STM_IfCond case *)
        admit.
      * (* STM_IfTrue case *)
        admit.
      * (* STM_IfFalse case *)
        admit.
  - (* ME_TApp case *)
    constructor.
    + intros e' Hstep.
      admit.
    + intros em' Hstep_m.
      admit.
  - (* ME_Unit case *)
    constructor.
    + intros e' Hstep.
      inversion Hstep.
    + intros em' Hstep_m.
      inversion Hstep_m.
Qed.
 *)
