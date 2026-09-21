import StlcSfl.StlcCommon

namespace Stlc

inductive Ty where
  | bool
  | arrow (T₁ T₂ : Ty)

inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (T : Ty) (t : Tm)
  | tru
  | fls
  | ite (c t e : Tm)

syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

namespace Elab

open StlcCommon
open Lean Meta Elab Term

def language : Language where
  tyType := ``Ty
  tmType := ``Tm
  arrowCtor := ``Ty.arrow
  varCtor := ``Tm.var
  appCtor := ``Tm.app
  absCtor := ``Tm.abs

  -- defined later
  subst := `Stlc.subst
  hasType := `Stlc.HasType

def boolTyHandler : TyElabHandler :=
  fun _recur k T => do
    match T with
    | `(stlcTy| Bool) =>
        return mkConst ``Ty.bool
    | _ => k T

def tyHandlers : TyElabHandler :=
  boolTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy unsupportedTy

def boolTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| true) => do
        return (mkConst ``Tm.tru, free)
    | `(stlcTm| false) => do
        return (mkConst ``Tm.fls, free)
    | `(stlcTm| Bool) => do
        throwError "`Bool` is not a valid term."
    | `(stlcTm| if $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite) c t e, free)
    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  boolTmHandler.orElse (commonTmHandler language elabTy)

partial def elabTm : TmElab :=
  tmHandlers elabTm unsupportedTm

scoped elab_rules (kind := StlcCommon.tyBracket) : term
  | `(<{ $T:stlcTy }>) => elabTy T

scoped elab_rules (kind := StlcCommon.tmBracket) : term
  | `(<{ $t:stlcTm }>) => do
      let (t, _) ← elabTm [] [] t
      return t

def elabCtx : CtxElab := elabCtxCommon language elabTy

scoped elab_rules (kind := StlcCommon.ctxBracket) : term
  | `(<{ $Γ:stlcCtx }>) => do
      let (Γ, _) ← elabCtx Γ
      return Γ

scoped elab_rules (kind := StlcCommon.judgeBracket) : term
  | `(<{ $Γ:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      let (Γ, scope) ← elabCtx Γ
      let (t, _) ← elabTm scope [] t
      let T ← elabTy T
      language.mkHasType Γ t T

end Elab

open scoped Elab

namespace Delab

open StlcCommon Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.bool]
private def Ty.unexpandBool : Unexpander
  | _ => do
    let T ← `(stlcTy| $(mkIdent `Bool):ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Tm.tru]
private def Tm.unexpandTru : Unexpander
  | _ => do
    let t ← `(stlcTm| $(mkIdent `true):ident)
    `(<{ $t:stlcTm }>)

@[app_unexpander Tm.fls]
private def Tm.unexpandFls : Unexpander
  | _ => do
    let t ← `(stlcTm| $(mkIdent `false):ident)
    `(<{ $t:stlcTm }>)

private def reservedNames : String → Bool
  | "true" | "false" | "Bool" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.ite]
private def Tm.unexpandIte : Unexpander
  | `($_ $c $t $e) =>
      `(<{ if $(getTm c) then $(getTm t) else $(getTm e) }>)
  | _ => throw ()

end Delab


/--
info: <{ λ x : Bool . λ y : Bool . x }> : Tm
---
warning: Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check <{ λ x : Bool . λ y : Bool . x }>

/-- info: <{ Bool → Bool }> : Ty -/
#guard_msgs in
#check <{ Bool → Bool }>

/-- info: <{ Bool → Bool → Bool }> : Ty -/
#guard_msgs in
#check <{ Bool → Bool → Bool }>

/-- info: <{ x }> : Tm -/
#guard_msgs in
#check (<{ x }> : Tm)

example (x : Tm) : (<{ x }> : Tm) = x := rfl

example (x : String) : (<{ x }> : Tm) = Tm.var "x" := rfl

/-- info: <{ x y }> : Tm -/
#guard_msgs in
#check <{ x y }>

/-- info: <{ x y (x y) }> : Tm -/
#guard_msgs in
#check <{ (x y) (x y) }>

/-- info: <{ x (y x) y x y }> : Tm -/
#guard_msgs in
#check <{ x (y x) y x y }>

/-- info: <{ λ x : Bool . x }> : Tm -/
#guard_msgs in
#check <{ λ x : Bool . x }>

/-- info: <{ (λ x : Bool . x) y }> : Tm -/
#guard_msgs in
#check <{ (λ x : Bool . x) y }>

/-- info: <{ if x then x else x }> : Tm -/
#guard_msgs in
#check <{ if x then x else x }>

/-- info: <{ if x y then x else x }> : Tm -/
#guard_msgs in
#check <{ if x y then x else x }>

/-- info: <{ if x y then x else x }> : Tm -/
#guard_msgs in
#check <{ if (x y) then x else x }>

/-- info: <{ if x then if x then y else x else y z }> : Tm -/
#guard_msgs in
#check <{ if x then if x then y else x else y z }>

/-- info: <{ (if x then if x then y else x else y) z }> : Tm -/
#guard_msgs in
#check <{ (if x then if x then y else x else y) z }>

/-- info: <{ λ z : Bool . z z }> : Tm -/
#guard_msgs in
#check <{ λ ~"z" : Bool . z z }>

/--
info: fun x z => <{ λ z : x . z z }> : Ty → String → Tm
---
warning: Variable name `z` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _z

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check fun (x : Ty) (z : String) => <{ λ z : x . z z }>

/-- info: Tm.abs "z" Ty.bool (((Tm.var "zzz").app (Tm.var "zzz")).app (Tm.var "z")) -/
#guard_msgs in
set_option pp.notation false in
#reduce let p := Tm.var "zzz"; <{ λ z : Bool . p p z }>

example : (<{ Bool → Bool → Bool }> : Ty) =
    Ty.arrow Ty.bool (Ty.arrow Ty.bool Ty.bool) := rfl

example : (<{ (Bool → Bool) → Bool }> : Ty) =
    Ty.arrow (Ty.arrow Ty.bool Ty.bool) Ty.bool := rfl

example : (<{ x y z }> : Tm) =
    Tm.app (Tm.app (Tm.var "x") (Tm.var "y")) (Tm.var "z") := rfl

example : (<{ (if x then y else z) x }> : Tm) =
    Tm.app (Tm.ite (Tm.var "x") (Tm.var "y") (Tm.var "z")) (Tm.var "x") := rfl

example : (<{ true }> : Tm) = Tm.tru := rfl

example : (<{ false }> : Tm) = Tm.fls := rfl

example : (<{ if x then y else z }> : Tm) =
    Tm.ite (Tm.var "x") (Tm.var "y") (Tm.var "z") := rfl

example (t : Tm) : (<{ t }> : Tm) = t := rfl

example (T : Ty) : (<{ T }> : Ty) = T := rfl

example (binder : String) : (<{ λ binder : Bool . binder }> : Tm) =
    Tm.abs "binder" Ty.bool (Tm.var "binder") := rfl

example (binder : String) (term : Tm) : (<{ λ binder : Bool . true }> : Tm) =
    Tm.abs "binder" Ty.bool Tm.tru := rfl

example (t u : Tm) : (<{ ~(Tm.app t u) }> : Tm) = Tm.app t u := rfl

/--
expected a Lean identifier of type `PartialMap String Ty`
  ⏎
  `Bool` is not a valid term.
  ⏎
  Type mismatch
    <{ Bool }>
  has type
    Ty
  but is expected to have type
    Tm
-/
#guard_msgs (substring := true) in
#check (<{ Bool }> : Tm)

/-- info: (Ty.bool.arrow Ty.bool).arrow Ty.bool : Ty -/
#guard_msgs in
set_option pp.notation false in
#check <{ (Bool → Bool) → Bool }>

/-- info: Stlc.Tm.var "true" : Tm -/
#guard_msgs in
#check Tm.var "true"

/-- info: Stlc.Tm.var "false" : Tm -/
#guard_msgs in
#check Tm.var "false"

/-- info: Stlc.Tm.var "Bool" : Tm -/
#guard_msgs in
#check Tm.var "Bool"

/-- info: <{ x }> : Tm -/
#guard_msgs in
#check Tm.var "x"

/-- info: <{ «if» }> : Tm -/
#guard_msgs in
#check Tm.var "if"

/-- info: <{ succ }> : Tm -/
#guard_msgs in
#check Tm.var "succ"

/-- info: Stlc.Tm.var "x-y" : Tm -/
#guard_msgs in
#check Tm.var "x-y"

/-- info: Stlc.Tm.var "1x" : Tm -/
#guard_msgs in
#check Tm.var "1x"

/-- info: Stlc.Tm.var "_" : Tm -/
#guard_msgs in
#check Tm.var "_"

/-- info: <{ x y z (λ x : Bool . x y (λ x : Bool . x)) }> : Tm -/
#guard_msgs in
#check (<{ x y z (λ x : Bool . x y (λ x : Bool . x))}>)

/--
error: Ambiguous term
  <{ x }>
Possible interpretations:
  x : PartialMap String Ty
  ⏎
  x : Tm
  ⏎
  x : Ty
---
info: fun x => sorry : (x : Ty) → ?m.3 x
-/
#guard_msgs in
#check fun x => <{ x }>

/--
info: fun x => <{ x }> : String → Tm
---
warning: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check fun (x : String) => <{ x }>
-- object Tm.var "x"

/-- info: fun x => x : Tm → Tm -/
#guard_msgs in
#check fun (x : Tm) => <{ x }>
-- Lean antiquotation

inductive Tm.IsValue : Tm → Prop where
  | abs (x : String) (T₂ : Ty) (t₁ : Tm) : IsValue <{ λ ~x : T₂. t₁ }>
  | tru : IsValue <{ true }>
  | fls : IsValue <{ false }>

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  | .var y =>
      if x = y then s else t
  | .abs y T t₁ =>
      if x = y then t else <{ λ ~y : T . [~x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([~x := s] t₁) ([~x := s] t₂) }>
  | .tru => .tru
  | .fls => .fls
  | .ite t₁ t₂ t₃ =>
      <{ if [~x := s] t₁ then [~x := s] t₂ else [~x := s] t₃ }>

open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst

section

variable (x y : String) (s t t₁ t₂ t₃ : Tm) (T : Ty)

@[simp] theorem subst_var_eq : <{ [~x := s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [~x := s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [~x := s] (λ ~x : T . t) }> = <{ λ ~x : T . t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [~x := s] (λ ~y : T . t) }> = <{ λ ~y : T . [~x := s] t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [~x := s] (t₁ t₂) }> = <{ ([~x := s] t₁) ([~x := s] t₂) }> := rfl

@[simp] theorem subst_tru : <{ [~x := s] true }> = <{ true }> := rfl

@[simp] theorem subst_fls : <{ [~x := s] false }> = <{ false }> := rfl

@[simp] theorem subst_ite :
    <{ [~x := s] (if t₁ then t₂ else t₃) }> =
      <{ if [~x := s] t₁ then [~x := s] t₂ else [~x := s] t₃ }> := rfl

end

/-- info: <{ [x := x] x }> : Tm -/
#guard_msgs in
#check <{ [x := x] x }>

/-- info: <{ [x := x] [x := y] z }> : Tm -/
#guard_msgs in
#check <{ [x := x] [x := y] z }>

/--
info: <{ [x := x] (λ y : Bool . x) }> : Tm
---
warning: Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check <{ [x := x] (λ y : Bool . x) }>

/-- info: <{ [x := x] (λ y : Bool . x y) }> : Tm -/
#guard_msgs in
#check <{ [x := x] (λ y : Bool . x y) }>

/-- info: <{ [x := x] (λ y : Bool . [x := x] x y) }> : Tm -/
#guard_msgs in
#check <{ [x := x] (λ y : Bool . ([x := x] x) y) }>

/-- info: <{ [x := z] y [x := z] x }> : Tm -/
#guard_msgs in
#check <{ ([x := z] y) ([x := z] x) }>

/-- info: <{ [x := λ y : Bool . y] (x z) }> : Tm -/
#guard_msgs in
#check <{ [x := (λ y : Bool . y)] (x z) }>

abbrev Context := PartialMap String Ty

inductive HasType : Context → Tm → Ty → Prop where
  | var (Γ : Context) (x : String) (T₁ : Ty)
      (h : Γ[x] = some T₁) :
      <{ Γ ⊢ ~(Tm.var x) ⦂ T₁ }>
  | abs (Γ : Context) (x : String)
      (T₁ T₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ ~T₂ ; Γ ⊢ t₁ ⦂ T₁ }>) :
      <{ Γ ⊢ λ ~x : T₂ . t₁ ⦂ T₂ → T₁ }>
  | app (Γ : Context) (T₁ T₂ : Ty)
      (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ T₂ → T₁ }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ T₂ }>) :
      <{ Γ ⊢ t₁ t₂ ⦂ T₁ }>
  | tru (Γ : Context) :
       <{ Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
       <{ Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (T₁ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Bool }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ T₁ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ T₁ }>) :
      <{ Γ ⊢ if t₁ then t₂ else t₃ ⦂ T₁ }>


open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander := StlcCommon.Delab.unexpandHasType

section

/-- info: <{ ∅ ⊢ true ⦂ Bool }> : Prop -/
#guard_msgs in
#check <{ ∅ ⊢ true ⦂ Bool }>

/-- info: <{ x ↦ Bool ; ∅ ⊢ x ⦂ Bool }> : Prop -/
#guard_msgs in
#check HasType
  (PartialMap.update (∅ : Context) "x" Ty.bool)
  (Tm.var "x")
  Ty.bool

/-- info: fun Γ t T => <{ Γ ⊢ t ⦂ T }> : Context → Tm → Ty → Prop -/
#guard_msgs in
#check fun (Γ : Context) (t : Tm) (T : Ty) => <{ Γ ⊢ t ⦂ T }>

end

end Stlc
