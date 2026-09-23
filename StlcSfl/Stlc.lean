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
  tyHandlers elabTy <| unsupportedTy language

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

def elabCtx : CtxElab := elabCtxCommon language elabTy

@[scoped term_elab StlcCommon.bracket]
def elabBracket : TermElab :=
  fun stx expectedType? => do
    let `(<{ $q:stlcQuoted }>) := stx
      | throwUnsupportedSyntax
    elabQuoted language elabTy elabTm elabCtx q expectedType?

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
info: <{ λ X : Bool . λ X : Bool . X }> : Tm
---
warning: Variable name `X` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _X

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check <{ λ X : Bool . λ X : Bool . X }>


/--
info: Try this:
  [apply] ~"x"
---
error: unknown metalanguage name identifier `x`
-/
#guard_msgs in
#check <{ λ x : Bool . x }>


/-- info: <{ Bool → Bool }> : Ty -/
#guard_msgs in
#check <{ Bool → Bool }>

/-- info: <{ Bool → Bool → Bool }> : Ty -/
#guard_msgs in
#check <{ Bool → Bool → Bool }>

/-- info: <{ X }> : Tm -/
#guard_msgs in
#check (<{ X }> : Tm)

example (x : Tm) : (<{ x }> : Tm) = x := rfl

/--
warning: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (x : String) : (<{ X }> : Tm) = Tm.var "X" := rfl

example : (<{ X }> : Stlc.Tm) = Tm.var "X" := rfl

example (x : Tm) : (<{ x }> : Tm) = x := rfl

example (X : Tm) : (<{ ~X }> : Tm) = X := rfl

example (x : String) (τ : Ty) :
    <{ λ x : τ . ~(Tm.var x) }> =
      Tm.abs x τ (Tm.var x) := rfl

example (τ : Ty) :
    (<{ λ X : τ . X }>) =
      Tm.abs "X" τ (Tm.var "X") := rfl

/-- info: <{ X Y }> : Tm -/
#guard_msgs in
#check <{ X Y }>

/-- info: <{ X Y (X Y) }> : Tm -/
#guard_msgs in
#check <{ (X Y) (X Y) }>

/-- info: <{ X (Y X) Y X Y }> : Tm -/
#guard_msgs in
#check <{ X (Y X) Y X Y }>

/-- info: <{ λ X : Bool . X }> : Tm -/
#guard_msgs in
#check <{ λ X : Bool . X }>

/-- info: <{ (λ X : Bool . X) Y }> : Tm -/
#guard_msgs in
#check <{ (λ X : Bool . X) Y }>

/-- info: <{ if X then X else X }> : Tm -/
#guard_msgs in
#check <{ if X then X else X }>

/-- info: <{ if X Y then X else X }> : Tm -/
#guard_msgs in
#check <{ if X Y then X else X }>

/-- info: <{ if X Y then X else X }> : Tm -/
#guard_msgs in
#check <{ if (X Y) then X else X }>

/-- info: <{ if X then if X then Y else X else Y Z }> : Tm -/
#guard_msgs in
#check <{ if X then if X then Y else X else Y Z }>

/-- info: <{ (if X then if X then Y else X else Y) Z }> : Tm -/
#guard_msgs in
#check <{ (if X then if X then Y else X else Y) Z }>

/-- info: <{ λ ~"z" : Bool . Z Z }> : Tm -/
#guard_msgs in
#check <{ λ ~"z" : Bool . Z Z }>

/--
info: Try this:
  [apply] ~(Stlc.Tm.var z)
---
error: metalanguage term identifier `z` has type
    String
  but this position expects
    Tm
---
info: fun x z => sorry : (x : Ty) → (z : String) → ?m.2 x z
-/
#guard_msgs in
#check fun (x : Ty) (z : String) => <{ λ z : x . z z }>

/-- info: Stlc.Tm.var "z" : Tm -/
#guard_msgs in
#check <{~(Tm.var "z")}>

/-- info: Tm.abs "Z" Ty.bool (((Tm.var "ZZ").app (Tm.var "ZZ")).app (Tm.var "Z")) -/
#guard_msgs in
set_option pp.notation false in
#reduce let p := Tm.var "ZZ"; <{ λ Z : Bool . p p Z }>

example : (<{ Bool → Bool → Bool }> : Ty) =
    Ty.arrow Ty.bool (Ty.arrow Ty.bool Ty.bool) := rfl

example : (<{ (Bool → Bool) → Bool }> : Ty) =
    Ty.arrow (Ty.arrow Ty.bool Ty.bool) Ty.bool := rfl

example : (<{ X Y Z }> : Tm) =
    Tm.app (Tm.app (Tm.var "X") (Tm.var "Y")) (Tm.var "Z") := rfl

example : (<{ (if X then Y else Z) X }> : Tm) =
    Tm.app (Tm.ite (Tm.var "X") (Tm.var "Y") (Tm.var "Z")) (Tm.var "X") := rfl

example : (<{ true }> : Tm) = Tm.tru := rfl

example : (<{ false }> : Tm) = Tm.fls := rfl

example : (<{ if X then Y else Z }> : Tm) =
    Tm.ite (Tm.var "X") (Tm.var "Y") (Tm.var "Z") := rfl

example (t : Tm) : (<{ t }> : Tm) = t := rfl

example (τ : Ty) : (<{ τ }> : Ty) = τ := rfl

example (binder : String) : (<{ λ binder : Bool . ~(Tm.var "binder") }> : Tm) =
    Tm.abs binder Ty.bool (Tm.var "binder") := rfl

/--
warning: Variable name `X` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _X

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `term` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _term

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Variable name `X` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _X

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
example (X : String) (term : Tm) : (<{ λ X : Bool . true }> : Tm) =
    Tm.abs "X" .bool Tm.tru := rfl

example (t u : Tm) : (<{ ~(Tm.app t u) }> : Tm) = Tm.app t u := rfl

/-- error: `Bool` is not a valid term. -/
#guard_msgs in
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

/-- info: Stlc.Tm.var "x" : Tm -/
#guard_msgs in
#check Tm.var "x"

/-- info: <{ X }> : Tm -/
#guard_msgs in
#check Tm.var "X"

/-- info: Stlc.Tm.var "if" : Tm -/
#guard_msgs in
#check Tm.var "if"

/-- info: Stlc.Tm.var "succ" : Tm -/
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

/-- info: <{ X Y Z (λ X : Bool . X Y (λ X : Bool . X)) }> : Tm -/
#guard_msgs in
#check (<{ X Y Z (λ X : Bool . X Y (λ X : Bool . X))}>)

/--
error: ambiguous STLC quotation

This syntax has multiple valid interpretations:
  context, term, type

Add a Lean type annotation to select the intended interpretation.
---
info: fun x => sorry : (x : ?m.1) → ?m.3 x
-/
#guard_msgs in
#check fun x => <{ x }>

/--
error: this STLC quotation has no valid interpretation

Tried: context, term, type

Add a Lean type annotation to select an interpretation and obtain a more specific error.
---
info: fun x => sorry : (x : String) → ?m.2 x
-/
#guard_msgs in
#check fun (x : String) => <{ x }>

/-- info: fun x => x : Tm → Tm -/
#guard_msgs in
#check fun (x : Tm) => <{ x }>

inductive Tm.IsValue : Tm → Prop where
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : IsValue <{ λ x : τ₂ . t₁ }>
  | tru : IsValue <{ true }>
  | fls : IsValue <{ false }>

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  | .tru => .tru
  | .fls => .fls
  | .ite t₁ t₂ t₃ =>
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }>

open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst

section

variable (x y : String) (s t t₁ t₂ t₃ : Tm) (τ : Ty)

@[simp] theorem subst_var_eq : <{ [x := s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [x := s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [x := s] (λ x : τ . t) }> = <{ λ x : τ . t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [x := s] (λ y : τ . t) }> = <{ λ y : τ . [x := s] t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [x := s] (t₁ t₂) }> = <{ ([x := s] t₁) ([x := s] t₂) }> := rfl

@[simp] theorem subst_tru : <{ [x := s] true }> = <{ true }> := rfl

@[simp] theorem subst_fls : <{ [x := s] false }> = <{ false }> := rfl

@[simp] theorem subst_ite :
    <{ [x := s] (if t₁ then t₂ else t₃) }> =
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }> := rfl

end

/-- info: <{ [X := X] X }> : Tm -/
#guard_msgs in
#check <{ [X := X] X }>

/-- info: <{ [X := X] [X := Y] Z }> : Tm -/
#guard_msgs in
#check <{ [X := X] [X := Y] Z }>

/--
info: <{ [X := X] (λ Y : Bool . X) }> : Tm
---
warning: Variable name `Y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _Y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check <{ [X := X] (λ Y : Bool . X) }>

/-- info: <{ [X := X] (λ Y : Bool . X Y) }> : Tm -/
#guard_msgs in
#check <{ [X := X] (λ Y : Bool . X Y) }>

/-- info: <{ [X := X] (λ Y : Bool . [X := X] X Y) }> : Tm -/
#guard_msgs in
#check <{ [X := X] (λ Y : Bool . ([X := X] X) Y) }>

/-- info: <{ [X := Z] Y [X := Z] X }> : Tm -/
#guard_msgs in
#check <{ ([X := Z] Y) ([X := Z] X) }>

/--
info: <{ [X := λ Y : Bool . Z] (X Z) }> : Tm
---
warning: Variable name `Y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _Y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check <{ [X := (λ Y : Bool . Z)] (X Z) }>

abbrev Context := PartialMap String Ty

inductive HasType : Context → Tm → Ty → Prop where
  | var (Γ : Context) (x : String) (τ₁ : Ty)
      (h : Γ[x] = some τ₁) :
      <{ Γ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs (Γ : Context) (x : String)
      (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ ⊢ λ x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty)
      (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ τ₂ → τ₁ }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ ⊢ t₁ t₂ ⦂ τ₁ }>
  | tru (Γ : Context) :
       <{ Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
       <{ Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (τ₁ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Bool }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ τ₁ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ τ₁ }>) :
      <{ Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ₁ }>

open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander := StlcCommon.Delab.unexpandHasType

section

/-- info: <{ ∅ ⊢ true ⦂ Bool }> : Prop -/
#guard_msgs in
#check <{ ∅ ⊢ true ⦂ Bool }>

/-- info: <{ X ↦ Bool ; ∅ ⊢ X ⦂ Bool }> : Prop -/
#guard_msgs in
#check HasType
  (PartialMap.update (∅ : Context) "X" Ty.bool)
  (Tm.var "X")
  Ty.bool

/--
info: fun Γ t τ => <{ Z ↦ Bool ; Γ ⊢ t ⦂ τ }> : Context → Tm → Ty → Prop
---
warning: Variable name `Z` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _Z

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check fun (Γ : Context) (t : Tm) (τ : Ty) => <{ Z ↦ Bool ; Γ ⊢ t ⦂ τ }>

end

end Stlc
