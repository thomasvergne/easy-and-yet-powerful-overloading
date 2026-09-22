Require Import Stdlib.Strings.String.
Require Import Overloading.LangC.Maps.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require FunInd.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Arith.PeanoNat.
Open Scope string_scope.

Definition tyvar := nat.

Inductive type : Type :=
  | Ty_Nat
  | Ty_Bool
  | Ty_String
  | Ty_Tuple (t1 t2: type)
  | Ty_Var (v: tyvar)
  | Ty_Forall (t: type)
  | Ty_Arrow (arg ret : type).

Fixpoint tin (tv: tyvar) (t: type) : Prop :=
  match t with
  | Ty_Nat => False
  | Ty_Bool => False
  | Ty_String => False
  | Ty_Tuple t1 t2 => tin tv t1 \/ tin tv t2
  | Ty_Arrow t1 t2 => tin tv t1 \/ tin tv t2
  | Ty_Var v => v = tv
  | Ty_Forall t1 => tin (S tv) t1
  end.

Fixpoint type_shift (d c: nat) (t: type) : type :=
    match t with
    | Ty_Nat => Ty_Nat
    | Ty_Bool => Ty_Bool
    | Ty_String => Ty_String
    | Ty_Tuple t1 t2 => Ty_Tuple (type_shift d c t1) (type_shift d c t2)
    | Ty_Arrow t1 t2 => Ty_Arrow (type_shift d c t1) (type_shift d c t2)
    | Ty_Var k => if Nat.leb c k then Ty_Var (k + d) else Ty_Var k
    | Ty_Forall t1 => Ty_Forall (type_shift d (S c) t1)
    end.

Fixpoint apply_type (repl: type) (t: type) : type :=
  match t with
  | Ty_Nat => Ty_Nat
  | Ty_Bool => Ty_Bool
  | Ty_String => Ty_String
  | Ty_Tuple t3 t4 => Ty_Tuple (apply_type repl t3) (apply_type repl t4)
  | Ty_Arrow t3 t4 => Ty_Arrow (apply_type repl t3) (apply_type repl t4)
  | Ty_Var 0 => repl
  | Ty_Var (S k) => Ty_Var k
  | Ty_Forall t1 => Ty_Forall (apply_type (type_shift 1 0 repl) t1)
  end.

Inductive expr : Type :=
  | E_Const (n: nat)
  | E_Bool (b: bool)
  | E_String (s: string)
  | E_Var (x: string)
  | E_App (e1 e2: expr)
  | E_Add (e1 e2: expr)

  | E_TypeAbs (e: expr)
  | E_TypeApp (e: expr) (t: type)

  | E_Property (n: string) (t: type) (e1 e2: expr)
  | E_Over (e: expr) (name: string)

  | E_Abs (x: string) (t: type) (e: expr)
  | E_Let (x: string) (e1 e2: expr)

  | E_Pair (e1 e2: expr)
  | E_Fst (e: expr)
  | E_Snd (e: expr)

  | E_If (e1 e2 e3: expr).

Fixpoint apply_type_expr (repl: type) (e: expr) : expr :=
  match e with
  | E_Const n => E_Const n
  | E_Bool b => E_Bool b
  | E_String s => E_String s
  | E_Var x => E_Var x
  | E_App e1 e2 => E_App (apply_type_expr repl e1) (apply_type_expr repl e2)
  | E_Add e1 e2 => E_Add (apply_type_expr repl e1) (apply_type_expr repl e2)

  | E_TypeAbs e1 =>
      E_TypeAbs (apply_type_expr (type_shift 1 0 repl) e1)
  | E_TypeApp e1 t =>
      E_TypeApp (apply_type_expr repl e1) (apply_type repl t)

  | E_Property n t e1 e2 =>
      E_Property n (apply_type repl t)
        (apply_type_expr repl e1)
        (apply_type_expr repl e2)

  | E_Over e name =>
      E_Over (apply_type_expr repl e) name

  | E_Abs x t e => E_Abs x (apply_type repl t) (apply_type_expr repl e)
  | E_Let x e1 e2 => E_Let x (apply_type_expr repl e1) (apply_type_expr repl e2)
  | E_Pair e1 e2 => E_Pair (apply_type_expr repl e1) (apply_type_expr repl e2)
  | E_Fst e => E_Fst (apply_type_expr repl e)
  | E_Snd e => E_Snd (apply_type_expr repl e)
  | E_If e1 e2 e3 =>
      E_If (apply_type_expr repl e1) (apply_type_expr repl e2) (apply_type_expr repl e3)
  end.

Fixpoint subst_expr (x: string) (v: expr) (e: expr) : expr :=
  match e with
  | E_Const n => E_Const n
  | E_Bool b => E_Bool b
  | E_String s => E_String s
  | E_Var y => if String.eqb x y then v else E_Var y
  | E_App e1 e2 => E_App (subst_expr x v e1) (subst_expr x v e2)
  | E_Add e1 e2 => E_Add (subst_expr x v e1) (subst_expr x v e2)

  | E_Property n t e1 e2 => E_Property n t (subst_expr x v e1) (subst_expr x v e2)

    | E_TypeAbs e1 => E_TypeAbs (subst_expr x v e1)
  | E_TypeApp e1 t => E_TypeApp (subst_expr x v e1) t

  | E_Abs y t1 e1 => E_Abs y t1 (if String.eqb x y then e1 else subst_expr x v e1)
  | E_Let y e1 e2 => E_Let y (subst_expr x v e1) (if String.eqb x y then e2 else subst_expr x v e2)

  | E_Over e name => E_Over (subst_expr x v e) name

  (* Pair relateed substitution *)
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
  | E_Var x => E_Var x
  | E_App e1 e2 => E_App (subst_over name v e1) (subst_over name v e2)
  | E_Add e1 e2 => E_Add (subst_over name v e1) (subst_over name v e2)

  | E_TypeAbs e1 => E_TypeAbs (subst_over name v e1)
  | E_TypeApp e1 t => E_TypeApp (subst_over name v e1) t

  | E_Property n t e1 e2 =>
      E_Property n t
        (subst_over name v e1)
        (if String.eqb n name then e2 else subst_over name v e2)

  | E_Over e n =>
      if String.eqb n name
      then E_App v (subst_over name v e)
      else E_Over (subst_over name v e) n

  | E_Abs x t e => E_Abs x t (subst_over name v e)
  | E_Let x e1 e2 => E_Let x (subst_over name v e1) (subst_over name v e2)
  | E_Pair e1 e2 => E_Pair (subst_over name v e1) (subst_over name v e2)
  | E_Fst e => E_Fst (subst_over name v e)
  | E_Snd e => E_Snd (subst_over name v e)
  | E_If e1 e2 e3 => E_If (subst_over name v e1) (subst_over name v e2) (subst_over name v e3)
  end.

Definition context := partial_map type.

Record implementation := {
  impl_name: string;
  impl_scheme: type;
}.

Definition impls := list implementation.

Definition update_impls (Hnd: impls) (name: string) (sch: type) : impls :=
  (Build_implementation name sch) :: Hnd.

Definition apply_type_env (repl: type) (Gamma: context) : context :=
  fun x => match Gamma x with
           | Some t => Some (apply_type repl t)
           | None => None
           end.

Fixpoint apply_type_env_impls (repl: type) (Delta: impls) : impls :=
  match Delta with
  | [] => []
  | impl :: rest =>
      Build_implementation (impl_name impl) (apply_type repl (impl_scheme impl)) :: apply_type_env_impls repl rest
  end.

(* Fixpoint context_lookup (Delta: impls) (name: string) (t: type) : Prop :=
  match Delta with
  | [] => False
  | impl :: rest =>
      if String.eqb (impl_name impl) name then
        instantiate (impl_scheme impl) t
      else
        context_lookup rest name t
  end. *)

Inductive context_lookup : impls -> string -> type -> Prop :=
  | CL_Here : forall Delta name sch t,
      sch = t ->
      context_lookup (Build_implementation name sch :: Delta) name t
  | CL_There : forall Delta name name' sch t,
      name <> name' ->
      context_lookup Delta name t ->
      context_lookup (Build_implementation name' sch :: Delta) name t.

Inductive has_type : context -> impls -> expr -> type -> Prop :=
  | T_Const : forall Gamma Delta n,
      has_type Gamma Delta (E_Const n) Ty_Nat

  | T_Bool : forall Gamma Delta b,
      has_type Gamma Delta (E_Bool b) Ty_Bool

  | T_String : forall Gamma Delta s,
      has_type Gamma Delta (E_String s) Ty_String

  | T_Var : forall Gamma Delta x t,
      Gamma x = Some t ->
      has_type Gamma Delta (E_Var x) t

  | T_TypeAbs : forall Gamma Delta e t,
      has_type Gamma Delta e t ->
      has_type Gamma Delta (E_TypeAbs e) (Ty_Forall t)

  | T_TypeApp : forall Gamma Delta e T T2,
      has_type Gamma Delta e (Ty_Forall T) ->
      has_type Gamma Delta (E_TypeApp e T2) (apply_type T2 T)

  | T_Over : forall Gamma Delta e name t1 t2,
      has_type Gamma Delta e t1 ->
      context_lookup Delta name (Ty_Arrow t1 t2) ->
      has_type Gamma Delta (E_Over e name) t2

  | T_App : forall Gamma Delta e1 e2 t1 t2,
      has_type Gamma Delta e1 (Ty_Arrow t1 t2) ->
      has_type Gamma Delta e2 t1 ->
      has_type Gamma Delta (E_App e1 e2) t2

  | T_Add : forall Gamma Delta e1 e2,
      has_type Gamma Delta e1 Ty_Nat ->
      has_type Gamma Delta e2 Ty_Nat ->
      has_type Gamma Delta (E_Add e1 e2) Ty_Nat

  | T_Property : forall Gamma Delta n e1 e2 t tbody,
      has_type Gamma Delta e1 t ->
      has_type Gamma (update_impls Delta n t) e2 tbody ->
      has_type Gamma Delta (E_Property n t e1 e2) tbody

  | T_Abs : forall Gamma Delta x t1 t2 e,
      has_type (x |-> t1; Gamma) Delta e t2 ->
      has_type Gamma Delta (E_Abs x t1 e) (Ty_Arrow t1 t2)

  | T_Let : forall Gamma Delta x e1 e2 t1 t2,
      has_type Gamma Delta e1 t1 ->
      has_type (x |-> t1; Gamma) Delta e2 t2 ->
      has_type Gamma Delta (E_Let x e1 e2) t2

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
      value (E_Pair e1 e2)
  | V_TypeAbs : forall e,
      value (E_TypeAbs e).

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
  | ST_PropertyStep : forall n sch e1 e1' e2,
      step e1 e1' ->
      step (E_Property n sch e1 e2) (E_Property n sch e1' e2)

  | ST_TypeAppStep : forall e e' t,
      step e e' ->
      step (E_TypeApp e t) (E_TypeApp e' t)

  | ST_TypeAppAbs : forall e t,
      step
        (E_TypeApp (E_TypeAbs e) t)
        (apply_type_expr t e)

  | ST_PropertySubst : forall n sch v1 e2,
      value v1 ->
      step (E_Property n sch v1 e2) (subst_over n v1 e2)

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
