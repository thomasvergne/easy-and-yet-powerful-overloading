Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require FunInd.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Logic.FunctionalExtensionality.

Definition total_map (A: Type) := string -> A.
Definition partial_map (A: Type) := total_map (option A).
Definition itotal_map (A: Type) := nat -> A.
Definition ipartial_map (A: Type) := itotal_map (option A).

Definition t_empty {A: Type} (v: A) : total_map A :=
  fun _ => v.

Definition t_update {A: Type} (m: total_map A)
           (x: string) (v: A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

Definition empty {A: Type} : partial_map A :=
  t_empty None.

Definition update {A: Type} (m: partial_map A)
           (x: string) (v: A) : partial_map A :=
  t_update m x (Some v).

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, x constr, right associativity).

Lemma t_apply_empty : forall (A: Type) (x: string) (v: A),
    (_ !-> v) x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall (A: Type) (m: total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma t_update_neq : forall (A: Type) (m: total_map A) x1 x2 v,
    x2 <> x1 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update.
  apply not_eq_sym in H. apply String.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A: Type) (m: total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros. destruct (String.eqb x x0) eqn:Heq.
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (A: Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros. destruct (String.eqb x x0) eqn:Heq.
  - apply String.eqb_eq in Heq. subst. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A: Type) (m : total_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros. destruct (String.eqb_spec x1 x); destruct (String.eqb_spec x2 x); subst.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition it_empty {A: Type} (v: A) : itotal_map A :=
  fun _ => v.

Definition it_update {A: Type} (m: itotal_map A)
           (x: nat) (v: A) : itotal_map A :=
  fun x' => if Nat.eqb x x' then v else m x'.

Notation "'_' '&->' v" := (it_empty v)
  (at level 100, right associativity).

Notation "x '&->' v ';' m" := (it_update m x v)
  (at level 0, x constr, v at level 200, right associativity).

Lemma it_apply_empty : forall (A: Type) (x: nat) (v: A),
    (_ &-> v) x = v.
Proof.
  intros. unfold it_empty. reflexivity.
Qed.

Lemma it_update_eq : forall (A: Type) (m: itotal_map A) x v,
    (x &-> v ; m) x = v.
Proof.
  intros. unfold it_update. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Qed.

Lemma it_update_neq : forall (A: Type) (m: itotal_map A) x1 x2 v,
    x2 <> x1 ->
    (x1 &-> v ; m) x2 = m x2.
Proof.
  intros. unfold it_update.
  apply not_eq_sym in H. apply PeanoNat.Nat.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

Lemma it_update_shadow : forall (A: Type) (m: itotal_map A) x v1 v2,
    (x &-> v2 ; x &-> v1 ; m) = (x &-> v2 ; m).
Proof.
  intros. unfold it_update. apply functional_extensionality.
  intros. destruct (Nat.eqb x x0) eqn:Heq.
  - reflexivity.
  - reflexivity.
Qed.

Theorem it_update_same : forall (A: Type) (m : itotal_map A) x,
    (x &-> m x ; m) = m.
Proof.
  intros. unfold it_update. apply functional_extensionality.
  intros. destruct (Nat.eqb x x0) eqn:Heq.
  - apply PeanoNat.Nat.eqb_eq in Heq. subst. reflexivity.
  - reflexivity.
Qed.

Theorem it_update_permute : forall (A: Type) (m : itotal_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 &-> v1 ; x2 &-> v2 ; m) = (x2 &-> v2 ; x1 &-> v1 ; m).
Proof.
  intros. unfold it_update. apply functional_extensionality.
  intros. destruct (PeanoNat.Nat.eqb_spec x1 x); destruct (PeanoNat.Nat.eqb_spec x2 x); subst.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition iempty {A: Type} : ipartial_map A :=
  it_empty None.

Definition iupdate {A: Type} (m: ipartial_map A)
           (x: nat) (v: A) : ipartial_map A :=
  it_update m x (Some v).

Notation "x '|&->' v" := (iupdate iempty x v)
  (at level 0, x constr, v at level 200).

Notation "x '|&->' v ';' m" := (iupdate m x v)
  (at level 0, x constr, v at level 200, right associativity).

Lemma iapply_empty : forall (A: Type) (x: nat),
    @iempty A x = None.
Proof.
  intros. unfold iempty, it_empty. reflexivity.
Qed.

Lemma iupdate_eq : forall (A: Type) (m: ipartial_map A) x v,
    (x |&-> v ; m) x = Some v.
Proof.
  intros. unfold iupdate, it_update. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Qed.

Theorem iupdate_neq : forall (A: Type) (m: ipartial_map A) x1 x2 v,
    x2 <> x1 ->
    (x1 |&-> v ; m) x2 = m x2.
Proof.
  intros. unfold iupdate, it_update.
  apply not_eq_sym in H. apply PeanoNat.Nat.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

Lemma iupdate_shadow : forall (A: Type) (m: ipartial_map A) x v1 v2,
    (x |&-> v2 ; x |&-> v1 ; m) = (x |&-> v2 ; m).
Proof.
  intros. unfold iupdate, it_update. apply functional_extensionality.
  intros. destruct (PeanoNat.Nat.eqb x x0) eqn:Heq.
  - reflexivity.
  - reflexivity.
Qed.

Theorem iupdate_permute : forall (A: Type) (m: ipartial_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |&-> v1 ; x2 |&-> v2 ; m) = (x2 |&-> v2 ; x1 |&-> v1 ; m).
Proof.
  intros. unfold iupdate, it_update. apply functional_extensionality.
  intros. destruct (PeanoNat.Nat.eqb_spec x1 x); destruct (PeanoNat.Nat.eqb_spec x2 x); subst.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Notation "x '|->' v" := (update empty x v)
  (at level 0, x constr, v at level 200).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 0, x constr, v at level 200, right associativity).

Lemma eq_snd_pair : forall {A B: Type} (x : A) (y1 y2 : B),
    (x, y1) <> (x, y2) -> y1 <> y2.
Proof.
  intros A B x y1 y2 Hneq Heq.
  subst. apply Hneq. reflexivity.
Qed.

Lemma apply_empty : forall (A: Type) (x: string),
  @empty A x = None.
Proof.
  intros. unfold empty, t_empty. reflexivity.
Qed.

Lemma update_eq : forall (A: Type) (m: partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update, t_update. rewrite String.eqb_refl. reflexivity.
Qed.

Theorem update_neq : forall (A: Type) (m: partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x1 |-> v ; m) x2 = m x2.
Proof.
  intros. unfold update, t_update.
  apply not_eq_sym in H. apply String.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

Lemma update_shadow : forall (A: Type) (m: partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros. unfold update, t_update. apply functional_extensionality.
  intros. destruct (String.eqb x x0) eqn:Heq.
  - reflexivity.
  - reflexivity.
Qed.

Theorem update_permute : forall (A: Type) (m: partial_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros. unfold update, t_update. apply functional_extensionality.
  intros. destruct (String.eqb_spec x1 x); destruct (String.eqb_spec x2 x); subst.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition includedin {A: Type} (m1 m2 : partial_map A) :=
  forall x v, m1 x = Some v -> m2 x = Some v.

Definition t_includedin {A: Type} (m1 m2 : total_map A) :=
  forall x y, m1 x = y -> m2 x = y.

Lemma includedin_update : forall (A: Type) (m1 m2: partial_map A) (x: string) (v: A),
    includedin m1 m2 ->
    includedin (x |-> v ; m1) (x |-> v ; m2).
Proof.
  intros. unfold includedin in *. intros.
  unfold update, t_update in *.
  destruct (String.eqb_spec x x0).
  - inversion H0. subst. reflexivity.
  - apply H in H0. assumption.
Qed.

Definition partial_concat {A: Type} (m1 m2: partial_map A) : partial_map A :=
  fun x => match m1 x with
           | Some v => Some v
           | None => m2 x
           end.

Lemma diff_eq : forall {A: Type} (y : A) (x: option A),
    x = Some y ->
    x = None ->
    False.
Proof.
  intros A y x Heq Hnone.
  rewrite Heq in Hnone. inversion Hnone.
Qed.

Lemma cons_inj : forall (A : Type) (x : A) xs ys,
  x :: xs = x :: ys ->
  xs = ys.
Proof.
  intros A x xs ys H.
  inversion H. reflexivity.
Qed.

Lemma inj_cons : forall (A: Type) (x: A) xs ys,
  xs = ys ->
  x :: xs = x :: ys.
Proof.
  intros A x xs ys H.
  rewrite H. reflexivity.
Qed.
