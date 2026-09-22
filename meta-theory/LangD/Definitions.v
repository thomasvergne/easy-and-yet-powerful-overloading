Require Import Stdlib.Strings.String.
Require Import Overloading.LangD.Maps.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require FunInd.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Arith.PeanoNat.
Open Scope string_scope.

Scheme All for or.

Definition tyvar := string.

Inductive type : Type :=
  | Ty_Nat
  | Ty_Bool
  | Ty_String
  | Ty_Tuple (t1 t2: type)
  | Ty_Var (v: tyvar)
  | Ty_Arrow (arg ret : type).

Fixpoint subst_type (c: string) (repl: type) (t: type) : type :=
  match t with
  | Ty_Nat => Ty_Nat
  | Ty_Bool => Ty_Bool
  | Ty_String => Ty_String
  | Ty_Tuple t1 t2 => Ty_Tuple (subst_type c repl t1) (subst_type c repl t2)
  | Ty_Arrow t1 t2 => Ty_Arrow (subst_type c repl t1) (subst_type c repl t2)
  | Ty_Var k => if String.eqb c k then repl else Ty_Var k
  end.

Definition apply_type (binding: string) (repl: type) (t: type) : type :=
  subst_type binding repl t.

Inductive type_scheme : Type :=
  | Ty_Forall (vars: list tyvar) (t: type).

Definition apply_type_scheme (binding: string) (repl: type) (sch: type_scheme) : type_scheme :=
  match sch with
  | Ty_Forall vars t =>
      if List.existsb (String.eqb binding) vars then
        Ty_Forall vars t
      else
        Ty_Forall vars (apply_type binding repl t)
  end.

Inductive bound_check : string -> type -> Prop :=
    | BC_Arrow : forall x t1 t2,
        bound_check x t1 ->
        bound_check x t2 ->
        bound_check x (Ty_Arrow t1 t2)
    | BC_Tuple : forall x t1 t2,
        bound_check x t1 ->
        bound_check x t2 ->
        bound_check x (Ty_Tuple t1 t2)
    | BC_Var : forall x v,
        x <> v ->
        bound_check x (Ty_Var v)
    | BC_Nat : forall x,
        bound_check x Ty_Nat
    | BC_Bool : forall x,
        bound_check x Ty_Bool
    | BC_String : forall x,
        bound_check x Ty_String.

Inductive unifies : type -> type -> Prop :=
  | Unify_Refl : forall t,
      unifies t t
  | Unify_Var : forall v t,
      bound_check v t ->
      unifies (Ty_Var v) t
  | Unify_Arrow : forall t1 t2 t1' t2',
      unifies t1 t1' ->
      unifies t2 t2' ->
      unifies (Ty_Arrow t1 t2) (Ty_Arrow t1' t2')
  | Unify_Tuple : forall t1 t2 t1' t2',
      unifies t1 t1' ->
      unifies t2 t2' ->
      unifies (Ty_Tuple t1 t2) (Ty_Tuple t1' t2')
  | Unify_Nat : unifies Ty_Nat Ty_Nat
  | Unify_Bool : unifies Ty_Bool Ty_Bool
  | Unify_String : unifies Ty_String Ty_String.

Fixpoint instantiate_scheme (vars : list string) (types : list type) (t : type) : option type :=
  match vars, types with
  | [], [] => Some t
  | v :: vars', ty :: types' => instantiate_scheme vars' types' (apply_type v ty t)
  | _, _ => None
  end.

Definition instantiate (sch : type_scheme) (ts : list type) (T : type) : Prop :=
  match sch with
  | Ty_Forall vars t => instantiate_scheme vars ts t = Some T
  end.

Lemma scheme_has_instance : forall ts t,
  exists T, instantiate (Ty_Forall ts t) (repeat Ty_Nat (length ts)) T.
Proof.
  induction ts as [| v ts' IH]; intros t.
  - exists t. simpl. reflexivity.
  - simpl. destruct (IH (apply_type v Ty_Nat t)) as [T HT].
    exists T. simpl. exact HT.
Qed.

Lemma subst_type_same_var : forall c t,
  subst_type c (Ty_Var c) t = t.
Proof.
  intros c t.
  induction t; simpl; try reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - destruct (String.eqb_spec c v); subst; reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma instantiate_scheme_id : forall vars t,
  instantiate_scheme vars (map Ty_Var vars) t = Some t.
Proof.
  induction vars as [| v vars' IH]; intros t; simpl.
  - reflexivity.
  - unfold apply_type. rewrite subst_type_same_var.
    apply IH.
Qed.

Lemma instantiate_id : forall ts t,
  instantiate (Ty_Forall ts t) (map Ty_Var ts) t.
Proof.
  intros. unfold instantiate. apply instantiate_scheme_id.
Qed.

Inductive expr : Type :=
  | E_Const (n: nat)
  | E_Bool (b: bool)
  | E_String (s: string)
  | E_Var (x: string) (vars: list type)
  | E_OVar (x: string) (vars: list type)
  | E_App (e1 e2: expr)
  | E_Add (e1 e2: expr)

  | E_Property (n: string) (vars: list string) (t: type) (e: expr)

  | E_Abs (x: string) (t: type) (e: expr)
  | E_Let (x: string) (ts: list tyvar) (e1 e2: expr)

  | E_Pair (e1 e2: expr)
  | E_Fst (e: expr)
  | E_Snd (e: expr)

  | E_If (e1 e2 e3: expr).

Fixpoint subst_type_expr (c: string) (repl: type) (e: expr) : expr :=
  match e with
  | E_Const n => E_Const n
  | E_Bool b => E_Bool b
  | E_String s => E_String s
  | E_Var x ts => E_Var x (map (subst_type c repl) ts)
  | E_OVar x ts => E_OVar x (map (subst_type c repl) ts)
  | E_App e1 e2 => E_App (subst_type_expr c repl e1) (subst_type_expr c repl e2)
  | E_Add e1 e2 => E_Add (subst_type_expr c repl e1) (subst_type_expr c repl e2)
  | E_Property n tvs t e => E_Property n tvs (subst_type c repl t) (subst_type_expr c repl e)
  | E_Abs x t e => E_Abs x (subst_type c repl t) (subst_type_expr c repl e)
  | E_Let x ts e1 e2 => E_Let x ts (subst_type_expr c repl e1) (subst_type_expr c repl e2)
  | E_Pair e1 e2 => E_Pair (subst_type_expr c repl e1) (subst_type_expr c repl e2)
  | E_Fst e => E_Fst (subst_type_expr c repl e)
  | E_Snd e => E_Snd (subst_type_expr c repl e)
  | E_If e1 e2 e3 =>
      E_If (subst_type_expr c repl e1) (subst_type_expr c repl e2) (subst_type_expr c repl e3)
  end.

Definition apply_type_expr (b: string) (repl: type) (e: expr) : expr :=
  subst_type_expr b repl e.

Fixpoint subst_expr (x: string) (v: expr) (e: expr) : expr :=
  match e with
  | E_Const n => E_Const n
  | E_Bool b => E_Bool b
  | E_String s => E_String s
  | E_Var y ts => if String.eqb x y then v else E_Var y ts
  | E_App e1 e2 => E_App (subst_expr x v e1) (subst_expr x v e2)
  | E_Add e1 e2 => E_Add (subst_expr x v e1) (subst_expr x v e2)

  | E_OVar x ts => E_OVar x ts
  | E_Property n tvs t e => E_Property n tvs t (subst_expr x v e)

  | E_Abs y t1 e1 => E_Abs y t1 (if String.eqb x y then e1 else subst_expr x v e1)
  | E_Let y ts e1 e2 => E_Let y ts (subst_expr x v e1) (if String.eqb x y then e2 else subst_expr x v e2)

  | E_Pair e1 e2 => E_Pair (subst_expr x v e1) (subst_expr x v e2)
  | E_Fst e1 => E_Fst (subst_expr x v e1)
  | E_Snd e1 => E_Snd (subst_expr x v e1)

  | E_If e1 e2 e3 => E_If (subst_expr x v e1) (subst_expr x v e2) (subst_expr x v e3)
  end.

Fixpoint subst_over (name: string) (v: expr) (e: expr) : expr :=
  match e with
  | E_Const n => E_Const n
  | E_Bool b => E_Bool b
  | E_String s => E_String s
  | E_Var x ts => E_Var x ts
  | E_App e1 e2 => E_App (subst_over name v e1) (subst_over name v e2)
  | E_Add e1 e2 => E_Add (subst_over name v e1) (subst_over name v e2)

  | E_OVar x ts => if String.eqb name x then v else E_OVar x ts

  | E_Property n tvs t e =>
      E_Property n tvs t (if String.eqb name n then e else subst_over name v e)

  | E_Abs x t e => E_Abs x t (subst_over name v e)
  | E_Let x ts e1 e2 => E_Let x ts (subst_over name v e1) (subst_over name v e2)
  | E_Pair e1 e2 => E_Pair (subst_over name v e1) (subst_over name v e2)
  | E_Fst e => E_Fst (subst_over name v e)
  | E_Snd e => E_Snd (subst_over name v e)
  | E_If e1 e2 e3 => E_If (subst_over name v e1) (subst_over name v e2) (subst_over name v e3)
  end.

Definition context := list (string * type_scheme).

Definition empty : context := [].

Definition update_context (Gamma: context) (name: string) (sch: type_scheme) : context :=
    (name, sch) :: Gamma.

Fixpoint apply_type_env (b: string) (repl: type) (Gamma: context) : context :=
    match Gamma with
    | [] => []
    | (name, sch) :: rest =>
                        (name, apply_type_scheme b repl sch) :: apply_type_env b repl rest
  end.

Inductive more_specific : type -> type -> Prop :=
  | MS_Refl : forall t,
      more_specific t t
  | MS_Var : forall t v,
      more_specific t (Ty_Var v)
  | MS_Arrow : forall t1 t2 t1' t2',
      more_specific t1 t1' ->
      more_specific t2 t2' ->
      more_specific (Ty_Arrow t1 t2) (Ty_Arrow t1' t2')
  | MS_Tuple : forall t1 t2 t1' t2',
      more_specific t1 t1' ->
      more_specific t2 t2' ->
      more_specific (Ty_Tuple t1 t2) (Ty_Tuple t1' t2')
  | MS_Nat : more_specific Ty_Nat Ty_Nat
  | MS_Bool : more_specific Ty_Bool Ty_Bool
  | MS_String : more_specific Ty_String Ty_String.

Definition more_specific_scheme (sch1 sch2 : type_scheme) : Prop :=
  match sch1, sch2 with
  | Ty_Forall _ t1, Ty_Forall _ t2 => more_specific t1 t2
  end.

Definition strictly_more_specific_scheme (sch1 sch2 : type_scheme) : Prop :=
  more_specific_scheme sch1 sch2 /\ ~ more_specific_scheme sch2 sch1.

Lemma more_specific_scheme_refl : forall sch,
  more_specific_scheme sch sch.
Proof.
  destruct sch as [tvs t].
  simpl. apply MS_Refl.
Qed.

Hint Resolve more_specific_scheme_refl : core.

Inductive variable_lookup : context -> string -> type_scheme -> Prop :=
  | VL_Here : forall Gamma x sch,
      variable_lookup ((x, sch) :: Gamma) x sch
  | VL_There : forall Gamma x y sch sch',
      x <> y ->
      variable_lookup Gamma x sch ->
      variable_lookup ((y, sch') :: Gamma) x sch.

Hint Constructors variable_lookup : core.

Definition list_includedin (Gamma Gamma' : context) : Prop :=
    forall (prefix : context) x sch,
        variable_lookup (List.app prefix Gamma) x sch ->
        variable_lookup (List.app prefix Gamma') x sch.

Fixpoint not_in_properties (x: string) (e: expr) : Prop :=
  match e with
  | E_Property n _ _ e2 => n <> x /\ not_in_properties x e2
  | E_App e1 e2 | E_Add e1 e2 | E_Pair e1 e2 => not_in_properties x e1 /\ not_in_properties x e2
  | E_Fst e1 | E_Snd e1 => not_in_properties x e1
  | E_Abs _ _ e1 => not_in_properties x e1
  | E_Let _ _ e1 e2 => not_in_properties x e1 /\ not_in_properties x e2
  | E_If e1 e2 e3 => not_in_properties x e1 /\ not_in_properties x e2 /\ not_in_properties x e3
  | _ => True
  end.

Lemma variable_lookup_shadow_prefix : forall (prefix: context) Gamma x sch1 sch2 y T,
  variable_lookup (List.app prefix ((x, sch1) :: (x, sch2) :: Gamma)) y T ->
  variable_lookup (List.app prefix ((x, sch1) :: Gamma)) y T.
Proof.
  induction prefix as [| [z tz] prefix IH]; intros Gamma x sch1 sch2 y T Hlook; simpl in *.
  - inversion Hlook; subst.
    + apply VL_Here.
    + inversion H5; subst.
      * contradiction.
      * apply VL_There; assumption.
  - inversion Hlook; subst.
    + apply VL_Here.
    + apply VL_There; [assumption | apply IH with (sch2 := sch2); assumption].
Qed.

Lemma variable_lookup_permute_prefix : forall prefix Gamma x1 x2 sch1 sch2 y T,
  x1 <> x2 ->
  variable_lookup (List.app prefix ((x1, sch1) :: (x2, sch2) :: Gamma)) y T ->
  variable_lookup (List.app prefix ((x2, sch2) :: (x1, sch1) :: Gamma)) y T.
Proof.
  induction prefix as [| [z tz] prefix IH]; intros Gamma x1 x2 sch1 sch2 y T Hneq Hlook; simpl in *.
  - inversion Hlook; subst.
    + apply VL_There; [assumption | apply VL_Here].
    + inversion H5; subst.
      * apply VL_Here.
      * apply VL_There; [assumption | apply VL_There; assumption].
  - inversion Hlook; subst.
    + apply VL_Here.
    + apply VL_There; [assumption | apply IH; assumption].
Qed.

Lemma app_assoc_local : forall (A : Type) (l1 l2 l3 : list A),
        List.app (List.app l1 l2) l3 = List.app l1 (List.app l2 l3).
Proof.
    intros A l1 l2 l3.
    induction l1; simpl.
    - reflexivity.
    - rewrite IHl1. reflexivity.
Qed.

Lemma list_includedin_update : forall Gamma Gamma' x sch,
        list_includedin Gamma Gamma' ->
        list_includedin ((x, sch) :: Gamma) ((x, sch) :: Gamma').
Proof.
    intros Gamma Gamma' x sch Hinc prefix y sch' Hlookup.
    assert (Hsource :
            variable_lookup (List.app (List.app prefix [(x, sch)]) Gamma) y sch').
    { rewrite app_assoc_local.
        exact Hlookup. }
    assert (Htarget :
            variable_lookup (List.app (List.app prefix [(x, sch)]) Gamma') y sch').
    { apply (Hinc (List.app prefix [(x, sch)]) y sch').
        exact Hsource. }
    rewrite app_assoc_local in Htarget.
    exact Htarget.
Qed.

Lemma variable_lookup_weakening : forall Gamma Gamma' x sch,
  variable_lookup Gamma x sch ->
  variable_lookup (List.app Gamma Gamma') x sch.
Proof.
  intros Gamma Gamma' x sch H.
  induction H; simpl.
  - apply VL_Here.
  - apply VL_There; assumption.
Qed.

Definition properties := partial_map type_scheme.

Definition update_properties (Delta: properties) (name: string) (sch: type_scheme) : properties :=
    update Delta name sch.

Definition property_lookup (Delta: properties) (name: string) (t: type_scheme) : Prop :=
  Delta name = Some t.

Definition apply_type_env_Delta (b: string) (repl: type) (Delta: properties) : properties :=
    fun name =>
        match Delta name with
        | Some sch => Some (apply_type_scheme b repl sch)
        | None => None
        end.

Inductive has_type : context -> properties -> expr -> type -> Prop :=
  | T_Const : forall Gamma Delta n,
      has_type Gamma Delta (E_Const n) Ty_Nat

  | T_Bool : forall Gamma Delta b,
      has_type Gamma Delta (E_Bool b) Ty_Bool

  | T_String : forall Gamma Delta s,
      has_type Gamma Delta (E_String s) Ty_String

  | T_Var : forall Gamma Delta x sch t ts,
      variable_lookup Gamma x sch ->
      instantiate sch ts t ->
      has_type Gamma Delta (E_Var x ts) t

  | T_Over : forall Gamma Delta name sch t ts,
      property_lookup Delta name sch ->
      instantiate sch ts t ->
      has_type Gamma Delta (E_OVar name ts) t

  | T_App : forall Gamma Delta e1 e2 t1 t2,
      has_type Gamma Delta e1 (Ty_Arrow t1 t2) ->
      has_type Gamma Delta e2 t1 ->
      has_type Gamma Delta (E_App e1 e2) t2

  | T_Add : forall Gamma Delta e1 e2,
      has_type Gamma Delta e1 Ty_Nat ->
      has_type Gamma Delta e2 Ty_Nat ->
      has_type Gamma Delta (E_Add e1 e2) Ty_Nat

  | T_Property : forall Gamma Delta tvs n e2 t tbody,
      has_type Gamma (update_properties Delta n (Ty_Forall tvs t)) e2 tbody ->
      has_type Gamma Delta (E_Property n tvs t e2) tbody

  | T_Abs : forall Gamma Delta x t1 t2 e,
      has_type ((x, Ty_Forall [] t1) :: Gamma) Delta e t2 ->
      has_type Gamma Delta (E_Abs x t1 e) (Ty_Arrow t1 t2)

  | T_Let : forall Gamma Delta x ts e1 e2 t1 t2,
      (forall ts_args Tinst, instantiate (Ty_Forall ts t1) ts_args Tinst -> has_type Gamma Delta e1 Tinst) ->
      has_type ((x, Ty_Forall ts t1) :: Gamma) Delta e2 t2 ->
      has_type Gamma Delta (E_Let x ts e1 e2) t2

  | T_If : forall Gamma Delta e1 e2 e3 t,
      has_type Gamma Delta e1 Ty_Bool ->
      has_type Gamma Delta e2 t ->
      has_type Gamma Delta e3 t ->
      has_type Gamma Delta (E_If e1 e2 e3) t

  | T_Pair : forall Gamma Delta e1 e2 t1 t2,
      has_type Gamma Delta e1 t1 ->
      has_type Gamma Delta e2 t2 ->
      has_type Gamma Delta (E_Pair e1 e2) (Ty_Tuple t1 t2)

  | T_Fst : forall Gamma Delta e t1 t2,
      has_type Gamma Delta e (Ty_Tuple t1 t2) ->
      has_type Gamma Delta (E_Fst e) t1

  | T_Snd : forall Gamma Delta e t1 t2,
      has_type Gamma Delta e (Ty_Tuple t1 t2) ->
      has_type Gamma Delta (E_Snd e) t2.

Hint Constructors has_type: core.

Inductive value : expr -> Prop :=
  | V_Const : forall n,
      value (E_Const n)
  | V_Bool : forall b,
      value (E_Bool b)
  | V_String : forall s,
      value (E_String s)
  | V_Abs : forall x t e,
      value (E_Abs x t e)
  | V_Pair : forall e1 e2,
      value e1 ->
      value e2 ->
      value (E_Pair e1 e2).

Inductive step : expr -> expr -> Prop :=
  | ST_AppAbs : forall x t e v,
      value v ->
      step (E_App (E_Abs x t e) v) (subst_expr x v e)
  | ST_App1 : forall e1 e1' e2,
      step e1 e1' ->
      step (E_App e1 e2) (E_App e1' e2)
  | ST_App2 : forall v1 e2 e2',
      value v1 ->
      step e2 e2' ->
      step (E_App v1 e2) (E_App v1 e2')
  | ST_AddConstConst : forall n1 n2,
      step (E_Add (E_Const n1) (E_Const n2)) (E_Const (n1 + n2))
  | ST_Add1 : forall e1 e1' e2,
      step e1 e1' ->
      step (E_Add e1 e2) (E_Add e1' e2)
  | ST_Add2 : forall v1 e2 e2',
      value v1 ->
      step e2 e2' ->
      step (E_Add v1 e2) (E_Add v1 e2')

  | ST_Let : forall x ts e1 e1' e2,
      step e1 e1' ->
      step (E_Let x ts e1 e2) (E_Let x ts e1' e2)
  | ST_Let_V : forall x ts v e2,
      value v ->
      step (E_Let x ts v e2) (subst_expr x v e2)
  | ST_IfTrue : forall e2 e3,
      step (E_If (E_Bool true) e2 e3) e2
  | ST_IfFalse : forall e2 e3,
      step (E_If (E_Bool false) e2 e3) e3
  | ST_If : forall e1 e1' e2 e3,
      step e1 e1' ->
      step (E_If e1 e2 e3) (E_If e1' e2 e3)
  | ST_Pair1 : forall e1 e1' e2,
      step e1 e1' ->
      step (E_Pair e1 e2) (E_Pair e1' e2)

  | ST_Pair2 : forall v1 e2 e2',
      value v1 ->
      step e2 e2' ->
      step (E_Pair v1 e2) (E_Pair v1 e2')

  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      step (E_Fst (E_Pair v1 v2)) v1

  | ST_Fst : forall e e',
      step e e' ->
      step (E_Fst e) (E_Fst e')
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      step (E_Snd (E_Pair v1 v2)) v2

  | ST_Snd : forall e e',
      step e e' ->
      step (E_Snd e) (E_Snd e').

Hint Constructors step: core.

Definition relation (X : Type) := X -> X -> Prop.

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  not (exists t', R t t').

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Definition multistep := multi step.

Inductive expr_m : Type :=
  | EM_Const (n: nat)
  | EM_Bool (b: bool)
  | EM_String (s: string)
  | EM_Var (x: string) (vars: list type)
  | EM_App (e1 e2: expr_m)
  | EM_Add (e1 e2: expr_m)
  | EM_Abs (x: string) (t: type) (e: expr_m)
  | EM_Let (x: string) (ts: list tyvar) (e1 e2: expr_m)
  | EM_Pair (e1 e2: expr_m)
  | EM_Fst (e: expr_m)
  | EM_Snd (e: expr_m)
  | EM_If (e1 e2 e3: expr_m).

Fixpoint free (e: expr_m): list string :=
  match e with
  | EM_Const _ | EM_Bool _ | EM_String _ => []
  | EM_Var x _ => [x]
  | EM_App e1 e2 | EM_Add e1 e2 | EM_Pair e1 e2 => free e1 ++ free e2
  | EM_Abs x _ e1 => remove string_dec x (free e1)
  | EM_Let x _ e1 e2 => free e1 ++ remove string_dec x (free e2)
  | EM_Fst e1 | EM_Snd e1 => free e1
  | EM_If e1 e2 e3 => free e1 ++ free e2 ++ free e3
  end.

Inductive value_m : expr_m -> Prop :=
  | VM_Const : forall n, value_m (EM_Const n)
  | VM_Bool : forall b, value_m (EM_Bool b)
  | VM_String : forall s, value_m (EM_String s)
  | VM_Abs : forall x t e, value_m (EM_Abs x t e)
  | VM_Pair : forall v1 v2, value_m v1 -> value_m v2 -> value_m (EM_Pair v1 v2).

Hint Constructors value_m : core.

Fixpoint subst_m (x: string) (v: expr_m) (e: expr_m) : expr_m :=
  match e with
  | EM_Const n => EM_Const n
  | EM_Bool b => EM_Bool b
  | EM_String s => EM_String s
  | EM_Var y vars => if String.eqb x y then v else EM_Var y vars
  | EM_App e1 e2 => EM_App (subst_m x v e1) (subst_m x v e2)
  | EM_Add e1 e2 => EM_Add (subst_m x v e1) (subst_m x v e2)
  | EM_Abs y t e1 => EM_Abs y t (if String.eqb x y then e1 else subst_m x v e1)
  | EM_Let y ts e1 e2 => EM_Let y ts (subst_m x v e1) (if String.eqb x y then e2 else subst_m x v e2)
  | EM_Pair e1 e2 => EM_Pair (subst_m x v e1) (subst_m x v e2)
  | EM_Fst e1 => EM_Fst (subst_m x v e1)
  | EM_Snd e1 => EM_Snd (subst_m x v e1)
  | EM_If e1 e2 e3 => EM_If (subst_m x v e1) (subst_m x v e2) (subst_m x v e3)
  end.

Inductive step_m : expr_m -> expr_m -> Prop :=
  | STM_AppAbs : forall x t e v,
      value_m v ->
      step_m (EM_App (EM_Abs x t e) v) (subst_m x v e)
  | STM_App1 : forall e1 e1' e2,
      step_m e1 e1' ->
      step_m (EM_App e1 e2) (EM_App e1' e2)
  | STM_App2 : forall v1 e2 e2',
      value_m v1 ->
      step_m e2 e2' ->
      step_m (EM_App v1 e2) (EM_App v1 e2')
  | STM_AddConstConst : forall n1 n2,
      step_m (EM_Add (EM_Const n1) (EM_Const n2)) (EM_Const (n1 + n2))
  | STM_Add1 : forall e1 e1' e2,
      step_m e1 e1' ->
      step_m (EM_Add e1 e2) (EM_Add e1' e2)
  | STM_Add2 : forall v1 e2 e2',
      value_m v1 ->
      step_m e2 e2' ->
      step_m (EM_Add v1 e2) (EM_Add v1 e2')
  | STM_Let : forall x ts e1 e1' e2,
      step_m e1 e1' ->
      step_m (EM_Let x ts e1 e2) (EM_Let x ts e1' e2)
  | STM_Let_V : forall x ts v e2,
      value_m v ->
      step_m (EM_Let x ts v e2) (subst_m x v e2)
  | STM_IfTrue : forall e2 e3,
      step_m (EM_If (EM_Bool true) e2 e3) e2
  | STM_IfFalse : forall e2 e3,
      step_m (EM_If (EM_Bool false) e2 e3) e3
  | STM_If : forall e1 e1' e2 e3,
      step_m e1 e1' ->
      step_m (EM_If e1 e2 e3) (EM_If e1' e2 e3)
  | STM_Pair1 : forall e1 e1' e2,
      step_m e1 e1' ->
      step_m (EM_Pair e1 e2) (EM_Pair e1' e2)
  | STM_Pair2 : forall v1 e2 e2',
      value_m v1 ->
      step_m e2 e2' ->
      step_m (EM_Pair v1 e2) (EM_Pair v1 e2')
  | STM_FstPair : forall v1 v2,
      value_m v1 ->
      value_m v2 ->
      step_m (EM_Fst (EM_Pair v1 v2)) v1
  | STM_Fst : forall e e',
      step_m e e' ->
      step_m (EM_Fst e) (EM_Fst e')
  | STM_SndPair : forall v1 v2,
      value_m v1 ->
      value_m v2 ->
      step_m (EM_Snd (EM_Pair v1 v2)) v2
  | STM_Snd : forall e e',
      step_m e e' ->
      step_m (EM_Snd e) (EM_Snd e').

Hint Constructors step_m : core.

Definition context_m := list (string * type_scheme).

Inductive var_lookup_m : context_m -> string -> type_scheme -> Prop :=
  | VLM_Here : forall Gamma x sch,
      var_lookup_m ((x, sch) :: Gamma) x sch
  | VLM_There : forall Gamma x y sch sch',
      x <> y ->
      var_lookup_m Gamma x sch ->
      var_lookup_m ((y, sch') :: Gamma) x sch.

Hint Constructors var_lookup_m : core.

Inductive has_type_m : context_m -> expr_m -> type -> Prop :=
  | TM_Const : forall Gamma n,
      has_type_m Gamma (EM_Const n) Ty_Nat
  | TM_Bool : forall Gamma b,
      has_type_m Gamma (EM_Bool b) Ty_Bool
  | TM_String : forall Gamma s,
      has_type_m Gamma (EM_String s) Ty_String
  | TM_Var : forall Gamma x sch t ts,
      var_lookup_m Gamma x sch ->
      instantiate sch ts t ->
      has_type_m Gamma (EM_Var x ts) t
  | TM_App : forall Gamma e1 e2 t1 t2,
      has_type_m Gamma e1 (Ty_Arrow t1 t2) ->
      has_type_m Gamma e2 t1 ->
      has_type_m Gamma (EM_App e1 e2) t2
  | TM_Add : forall Gamma e1 e2,
      has_type_m Gamma e1 Ty_Nat ->
      has_type_m Gamma e2 Ty_Nat ->
      has_type_m Gamma (EM_Add e1 e2) Ty_Nat
  | TM_Abs : forall Gamma x t1 t2 e,
      has_type_m ((x, Ty_Forall [] t1) :: Gamma) e t2 ->
      has_type_m Gamma (EM_Abs x t1 e) (Ty_Arrow t1 t2)
  | TM_Let : forall Gamma x ts e1 e2 t1 t2,
      (forall ts_args Tinst, instantiate (Ty_Forall ts t1) ts_args Tinst -> has_type_m Gamma e1 Tinst) ->
      has_type_m ((x, Ty_Forall ts t1) :: Gamma) e2 t2 ->
      has_type_m Gamma (EM_Let x ts e1 e2) t2
  | TM_If : forall Gamma e1 e2 e3 t,
      has_type_m Gamma e1 Ty_Bool ->
      has_type_m Gamma e2 t ->
      has_type_m Gamma e3 t ->
      has_type_m Gamma (EM_If e1 e2 e3) t
  | TM_Pair : forall Gamma e1 e2 t1 t2,
      has_type_m Gamma e1 t1 ->
      has_type_m Gamma e2 t2 ->
      has_type_m Gamma (EM_Pair e1 e2) (Ty_Tuple t1 t2)
  | TM_Fst : forall Gamma e t1 t2,
      has_type_m Gamma e (Ty_Tuple t1 t2) ->
      has_type_m Gamma (EM_Fst e) t1
  | TM_Snd : forall Gamma e t1 t2,
      has_type_m Gamma e (Ty_Tuple t1 t2) ->
      has_type_m Gamma (EM_Snd e) t2.

Hint Constructors has_type_m : core.

Definition instance_env := list (string * list type * expr_m).

Inductive mono_expr (Omega: instance_env) : expr -> expr_m -> Prop :=
  | ME_Const : forall n,
      mono_expr Omega (E_Const n) (EM_Const n)
  | ME_Bool : forall b,
      mono_expr Omega (E_Bool b) (EM_Bool b)
  | ME_String : forall s,
      mono_expr Omega (E_String s) (EM_String s)
  | ME_Var : forall x ts,
      mono_expr Omega (E_Var x ts) (EM_Var x ts)
  | ME_OVar : forall n ts em,
      In (n, ts, em) Omega ->
      mono_expr Omega (E_OVar n ts) em
  | ME_App : forall e1 e2 em1 em2,
      mono_expr Omega e1 em1 ->
      mono_expr Omega e2 em2 ->
      mono_expr Omega (E_App e1 e2) (EM_App em1 em2)
  | ME_Add : forall e1 e2 em1 em2,
      mono_expr Omega e1 em1 ->
      mono_expr Omega e2 em2 ->
      mono_expr Omega (E_Add e1 e2) (EM_Add em1 em2)
  | ME_Abs : forall x t e em,
      mono_expr Omega e em ->
      mono_expr Omega (E_Abs x t e) (EM_Abs x t em)
  | ME_Let : forall x ts e1 e2 em1 em2,
      mono_expr Omega e1 em1 ->
      mono_expr Omega e2 em2 ->
      mono_expr Omega (E_Let x ts e1 e2) (EM_Let x ts em1 em2)
  | ME_Property : forall n tvs t e em,
      mono_expr Omega e em ->
      mono_expr Omega (E_Property n tvs t e) em
  | ME_Pair : forall e1 e2 em1 em2,
      mono_expr Omega e1 em1 ->
      mono_expr Omega e2 em2 ->
      mono_expr Omega (E_Pair e1 e2) (EM_Pair em1 em2)
  | ME_Fst : forall e em,
      mono_expr Omega e em ->
      mono_expr Omega (E_Fst e) (EM_Fst em)
  | ME_Snd : forall e em,
      mono_expr Omega e em ->
      mono_expr Omega (E_Snd e) (EM_Snd em)
  | ME_If : forall e1 e2 e3 em1 em2 em3,
      mono_expr Omega e1 em1 ->
      mono_expr Omega e2 em2 ->
      mono_expr Omega e3 em3 ->
      mono_expr Omega (E_If e1 e2 e3) (EM_If em1 em2 em3).

Hint Constructors mono_expr : core.

Definition instance_env_matches (Delta: properties) (Omega: instance_env) : Prop :=
  forall n sch ts Tinst em,
    property_lookup Delta n sch ->
    instantiate sch ts Tinst ->
    In (n, ts, em) Omega ->
    has_type_m [] em Tinst.

Definition instance_catalog := list (string * type_scheme * expr_m).

Definition is_most_specific_candidate (catalog : instance_catalog)
                                      (name : string) (ts : list type) (best_sch : type_scheme) : Prop :=
  forall n' sch' em',
    In (n', sch', em') catalog ->
    n' = name ->
    (exists T', instantiate sch' ts T') ->
    ~ strictly_more_specific_scheme sch' best_sch.

Definition valid_monomorphization (catalog : instance_catalog)
                                  (Omega : instance_env) : Prop :=
  forall name ts em,
    In (name, ts, em) Omega ->
    exists sch T,
      In (name, sch, em) catalog /\
      instantiate sch ts T /\
      is_most_specific_candidate catalog name ts sch /\
      has_type_m [] em T.

Inductive context_matches : context -> context_m -> Prop :=
  | CM_Nil : context_matches [] []
  | CM_Cons : forall Gamma Gamma_m x sch,
      context_matches Gamma Gamma_m ->
      context_matches ((x, sch) :: Gamma) ((x, sch) :: Gamma_m).

Fixpoint collect_ovars (e : expr) : list (string * list type) :=
  match e with
  | E_Const _ | E_Bool _ | E_String _ | E_Var _ _ => []
  | E_OVar n ts => [(n, ts)]
  | E_App e1 e2 | E_Add e1 e2 | E_Pair e1 e2 =>
      collect_ovars e1 ++ collect_ovars e2
  | E_Abs _ _ e | E_Property _ _ _ e | E_Fst e | E_Snd e =>
      collect_ovars e
  | E_Let _ _ e1 e2 =>
      collect_ovars e1 ++ collect_ovars e2
  | E_If e1 e2 e3 =>
      collect_ovars e1 ++ collect_ovars e2 ++ collect_ovars e3
  end.

Definition select_instance (catalog : instance_catalog)
                           (name : string) (ts : list type) (em : expr_m) : Prop :=
  exists sch T,
    In (name, sch, em) catalog /\
    instantiate sch ts T /\
    is_most_specific_candidate catalog name ts sch /\
    has_type_m [] em T.

Definition omega_covers (catalog : instance_catalog) (Omega : instance_env) (e : expr) : Prop :=
  valid_monomorphization catalog Omega /\
  forall name ts,
    In (name, ts) (collect_ovars e) ->
    exists em, In (name, ts, em) Omega.

Definition catalog_covers (catalog : instance_catalog) (e : expr) : Prop :=
  forall n ts,
    In (n, ts) (collect_ovars e) ->
    exists em, select_instance catalog n ts em.

Definition compatible_scheme (sch_Delta sch_C : type_scheme) : Prop :=
  forall ts T_Delta T_C,
    instantiate sch_Delta ts T_Delta ->
    instantiate sch_C ts T_C ->
    T_Delta = T_C.

Definition catalog_conforms (catalog : instance_catalog) (Delta : properties) : Prop :=
  forall n sch_C em,
    In (n, sch_C, em) catalog ->
    forall sch_Delta,
      property_lookup Delta n sch_Delta ->
      compatible_scheme sch_Delta sch_C.

Lemma catalog_conforms_implies_matches :
  forall catalog Delta Omega,
    catalog_conforms catalog Delta ->
    valid_monomorphization catalog Omega ->
    instance_env_matches Delta Omega.
Proof.
  intros catalog Delta Omega Hconf Hvalid.
  unfold instance_env_matches.
  intros n sch_Delta ts Tinst em Hlookup Hinst_Delta Hin_om.

  destruct (Hvalid n ts em Hin_om) as [sch_C [T_C [Hin_cat [Hinst_C [_ Htyp_m]]]]].

  assert (Hcompat : compatible_scheme sch_Delta sch_C).
  { eapply Hconf; eassumption. }

  assert (Heq : Tinst = T_C).
  { eapply Hcompat; eassumption. }
  subst Tinst.
  exact Htyp_m.
Qed.

Hint Constructors context_matches : core.
