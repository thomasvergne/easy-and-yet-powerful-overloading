Require Import Stdlib.Strings.String.
Require Import Overloading.LangA.Maps.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require FunInd.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Arith.PeanoNat.
Open Scope string_scope.

Inductive type : Type :=
  | Ty_Nat
  | Ty_Bool
  | Ty_String
  | Ty_Tuple (t1 t2: type)
  | Ty_Arrow : type -> type -> type.

Fixpoint apply_type (t1: type) (repl: nat) (t2: type) : type :=
  match t2 with
  | Ty_Nat => Ty_Nat
  | Ty_Bool => Ty_Bool
  | Ty_String => Ty_String
  | Ty_Tuple t1 t2 => Ty_Tuple (apply_type t1 repl t1) (apply_type t1 repl t2)
  | Ty_Arrow t3 t4 => Ty_Arrow (apply_type t1 repl t3) (apply_type t1 repl t4)
  end.

Definition context := partial_map type.
Definition impls := partial_map (list type).
Definition show_context := list type.

Inductive expr : Type :=
  | E_Const (n: nat)
  | E_Bool (b: bool)
  | E_String (s: string)
  | E_Var (x: string)
  | E_App (e1 e2: expr)
  | E_Add (e1 e2: expr)
  | E_Show (e: expr)
  | E_LetShow (t: type) (x: string) (e: expr)
  | E_Abs (x: string) (t: type) (e: expr)
  | E_Let (x: string) (e1 e2: expr)
  | E_Pair (e1 e2: expr)
  | E_Fst (e: expr)
  | E_Snd (e: expr)
  | E_If (e1 e2 e3: expr).

Inductive typed_expr : Type :=
  | TE_Const (n: nat)
  | TE_Bool (b: bool)
  | TE_String (s: string)
  | TE_Var (x: string) (t: type)
  | TE_App (e1 e2: typed_expr) (t: type)
  | TE_Add (e1 e2: typed_expr)
  | TE_Show (e: typed_expr) (t: type)
  | TE_LetShow (t: type) (x: string) (e: typed_expr)
  | TE_Abs (x: string) (t1 t2: type) (e: typed_expr)
  | TE_Let (x: string) (t1 t2: type) (e1 e2: typed_expr)
  | TE_Pair (e1 e2: typed_expr)
  | TE_Fst (e: typed_expr)
  | TE_Snd (e: typed_expr)
  | TE_If (e1 e2 e3: typed_expr) (t: type).

Fixpoint subst_expr (x: string) (v: expr) (e: expr) : expr :=
  match e with
  | E_Const n => E_Const n
  | E_Bool b => E_Bool b
  | E_String s => E_String s
  | E_Var y => if String.eqb x y then v else E_Var y
  | E_App e1 e2 => E_App (subst_expr x v e1) (subst_expr x v e2)
  | E_Add e1 e2 => E_Add (subst_expr x v e1) (subst_expr x v e2)
  | E_Show e1 => E_Show (subst_expr x v e1)
  | E_LetShow t y e1 => E_LetShow t y (if String.eqb x y then e1 else subst_expr x v e1)
  | E_Abs y t1 e1 => E_Abs y t1 (if String.eqb x y then e1 else subst_expr x v e1)
  | E_Let y e1 e2 => E_Let y (subst_expr x v e1) (if String.eqb x y then e2 else subst_expr x v e2)

  (* Pair relateed substitution *)
  | E_Pair e1 e2 => E_Pair (subst_expr x v e1) (subst_expr x v e2)
  | E_Fst e1 => E_Fst (subst_expr x v e1)
  | E_Snd e1 => E_Snd (subst_expr x v e1)

  | E_If e1 e2 e3 => E_If (subst_expr x v e1) (subst_expr x v e2) (subst_expr x v e3)
  end.

Fixpoint subst_typed_expr (x: string) (tv: typed_expr) (te: typed_expr) : typed_expr :=
  match te with
  | TE_Const n => TE_Const n
  | TE_Bool b => TE_Bool b
  | TE_String s => TE_String s
  | TE_Var y t => if String.eqb x y then tv else TE_Var y t
  | TE_App te1 te2 t => TE_App (subst_typed_expr x tv te1) (subst_typed_expr x tv te2) t
  | TE_Add te1 te2 => TE_Add (subst_typed_expr x tv te1) (subst_typed_expr x tv te2)
  | TE_Show te1 t => TE_Show (subst_typed_expr x tv te1) t
  | TE_LetShow t y te1 => TE_LetShow t y (if String.eqb x y then te1 else subst_typed_expr x tv te1)
  | TE_Abs y t1 t2 te1 => TE_Abs y t1 t2 (if String.eqb x y then te1 else subst_typed_expr x tv te1)
  | TE_Let y t1 t2 te1 te2 => TE_Let y t1 t2 (subst_typed_expr x tv te1) (if String.eqb x y then te2 else subst_typed_expr x tv te2)

  | TE_Pair te1 te2 => TE_Pair (subst_typed_expr x tv te1) (subst_typed_expr x tv te2)
  | TE_Fst te1 => TE_Fst (subst_typed_expr x tv te1)
  | TE_Snd te1 => TE_Snd (subst_typed_expr x tv te1)

  | TE_If te1 te2 te3 t => TE_If (subst_typed_expr x tv te1) (subst_typed_expr x tv te2) (subst_typed_expr x tv te3) t
  end.

Inductive has_type : context -> show_context -> expr -> type -> typed_expr -> Prop :=
  | T_Const : forall Gamma Delta n,
      has_type Gamma Delta (E_Const n) Ty_Nat (TE_Const n)

  | T_Bool : forall Gamma Delta b,
      has_type Gamma Delta (E_Bool b) Ty_Bool (TE_Bool b)

  | T_String : forall Gamma Delta s,
      has_type Gamma Delta (E_String s) Ty_String (TE_String s)

  | T_Var : forall Gamma Delta x t,
      Gamma x = Some t ->
      has_type Gamma Delta (E_Var x) t (TE_Var x t)

  | T_App : forall Gamma Delta e1 e2 t1 t2 te1 te2,
      has_type Gamma Delta e1 (Ty_Arrow t1 t2) te1 ->
      has_type Gamma Delta e2 t1 te2 ->
      has_type Gamma Delta (E_App e1 e2) t2 (TE_App te1 te2 t2)

  | T_Add : forall Gamma Delta e1 e2 te1 te2,
      has_type Gamma Delta e1 Ty_Nat te1 ->
      has_type Gamma Delta e2 Ty_Nat te2 ->
      has_type Gamma Delta (E_Add e1 e2) Ty_Nat (TE_Add te1 te2)

  | T_Show : forall Gamma Delta e te t,
      In t Delta ->
      has_type Gamma Delta e t te ->
      has_type Gamma Delta (E_Show e) Ty_String (TE_Show te t)

  | T_LetShow : forall Gamma Delta t x e te,
      has_type Gamma Delta e Ty_String te ->
      has_type Gamma (t :: Delta) (E_LetShow t x e) t (TE_LetShow t x te)

  | T_Abs : forall Gamma Delta x t1 t2 e te,
      has_type (x |-> t1; Gamma) Delta e t2 te ->
      has_type Gamma Delta (E_Abs x t1 e) (Ty_Arrow t1 t2) (TE_Abs x t1 t2 te)

  | T_Let : forall Gamma Delta x e1 e2 t1 t2 te1 te2,
      has_type Gamma Delta e1 t1 te1 ->
      has_type (x |-> t1; Gamma) Delta e2 t2 te2 ->
      has_type Gamma Delta (E_Let x e1 e2) t2 (TE_Let x t1 t2 te1 te2)

  | T_If : forall Gamma Delta e1 e2 e3 te1 te2 te3 t,
      has_type Gamma Delta e1 Ty_Bool te1 ->
      has_type Gamma Delta e2 t te2 ->
      has_type Gamma Delta e3 t te3 ->
      has_type Gamma Delta (E_If e1 e2 e3) t (TE_If te1 te2 te3 t)

  | T_Pair : forall Gamma Delta e1 e2 t1 t2 te1 te2,
      has_type Gamma Delta e1 t1 te1 ->
      has_type Gamma Delta e2 t2 te2 ->
      has_type Gamma Delta (E_Pair e1 e2) (Ty_Tuple t1 t2) (TE_Pair te1 te2)

  | T_Fst : forall Gamma Delta e t1 t2 te,
      has_type Gamma Delta e (Ty_Tuple t1 t2) te ->
      has_type Gamma Delta (E_Fst e) t1 (TE_Fst te)

  | T_Snd : forall Gamma Delta e t1 t2 te,
      has_type Gamma Delta e (Ty_Tuple t1 t2) te ->
      has_type Gamma Delta (E_Snd e) t2 (TE_Snd te).

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
  | ST_Show : forall e e',
      step e e' ->
      step (E_Show e) (E_Show e')
  | ST_LetShow : forall t x e v,
      value v ->
      step (E_LetShow t x (E_Show v)) (subst_expr x v e)
  | ST_LetShow_Eval : forall t x e e',
      step e e' ->
      step (E_LetShow t x e) (E_LetShow t x e')
  | ST_Let : forall x e1 e1' e2,
      step e1 e1' ->
      step (E_Let x e1 e2) (E_Let x e1' e2)
  | ST_Let_V : forall x v e2,
      value v ->
      step (E_Let x v e2) (subst_expr x v e2)
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
