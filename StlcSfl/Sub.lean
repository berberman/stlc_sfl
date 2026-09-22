import StlcSfl.StlcCommon

namespace StlcSub

inductive Ty : Type where
  | top   : Ty
  | bool  : Ty
  | base  : String → Ty
  | arrow : Ty → Ty → Ty
  | unit  : Ty
  | prod : Ty → Ty → Ty

inductive Tm : Type where
  | var : String → Tm
  | app : Tm → Tm → Tm
  | abs : String → Ty → Tm → Tm
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm
  | unit : Tm
  | pair : Tm → Tm → Tm
  | fst : Tm → Tm
  | snd : Tm → Tm

scoped syntax:50 stlcTy:51 " × " stlcTy:50 : stlcTy
scoped syntax:max " ⊤ " : stlcTy
scoped syntax:50 "if " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm
scoped syntax:max " ( " stlcTm:60 " , " stlcTm:60 " ) " : stlcTm

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
  subst := `StlcSub.subst
  hasType := `StlcSub.HasType

def subTyHandler : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| ⊤) => do
        return mkConst ``Ty.top
    | `(stlcTy| Bool) => do
        return mkConst ``Ty.bool
    | `(stlcTy| Unit) => do
        return mkConst ``Ty.unit
    | `(stlcTy| $T₁:stlcTy × $T₂:stlcTy) => do
        let T₁ ← recur T₁
        let T₂ ← recur T₂
        return mkApp2 (mkConst ``Ty.prod) T₁ T₂
    | _ => k T

/--
Make unresolved type identifiers "base types".
This must run after `commonTyHandler`
so a Lean variable `τ : Ty` is implicitly antiquoted first.
-/

def baseTyHandler : TyElabHandler :=
  fun _recur k T => do
    match T with
    | `(stlcTy| $id:ident) => do
        match classifyIdent? id with
        | some (.object, name) =>
          return mkApp (mkConst ``Ty.base) (mkStrLit name)
        | _ => k T
    | _ => k T

def tyHandlers : TyElabHandler :=
  subTyHandler.orElse ((commonTyHandler language).orElse baseTyHandler)

partial def elabTy : TyElab := tyHandlers elabTy  <| unsupportedTy language

def subTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| true) =>
        return (mkConst ``Tm.tru, free)
    | `(stlcTm| false) =>
        return (mkConst ``Tm.fls, free)
    | `(stlcTm| Bool) =>
        throwError "`Bool` is not a valid term."
    | `(stlcTm| Unit) =>
        throwError "`Unit` is not a valid term."
    | `(stlcTm| if $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite) c t e, free)
    | `(stlcTm| unit) =>
        return (mkConst ``Tm.unit, free)
    | `(stlcTm| ($t₁:stlcTm, $t₂:stlcTm)) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.pair) t₁ t₂, free)
    | `(stlcTm| fst $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.fst) t, free)
    | `(stlcTm| snd $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.snd) t, free)
    | _ => k Γ free t

def tmHandlers : TmElabHandler := subTmHandler.orElse (commonTmHandler language elabTy)


partial def elabTm : TmElab := tmHandlers elabTm unsupportedTm

scoped elab_rules (kind := StlcCommon.tyBracket) : term
  | `(<{ $T:stlcTy }>) => elabTy T


scoped elab_rules (kind := StlcCommon.tmBracket) : term
  | `(<{ $t:stlcTm }>) => do
      let (t, _) ← elabTm [] [] t
      return t


def elabCtx : CtxElab :=
  elabCtxCommon language elabTy


scoped elab_rules (kind := StlcCommon.ctxBracket) : term
  | `(<{ $Γ:stlcCtx }>) => do
      let (Γ, _) ← elabCtx Γ
      return Γ

scoped elab_rules
    (kind := StlcCommon.judgeBracket) : term
  | `(<{ $Γ:stlcCtx ⊢ $t:stlcTm ⦂ $T:stlcTy }>) => do
      let (Γ, scope) ← elabCtx Γ
      let (t, _) ← elabTm scope [] t
      let T ← elabTy T
      language.mkHasType Γ t T

end Elab

open scoped Elab

namespace Delab

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator


@[app_unexpander Ty.top]
private def Ty.unexpandTop : Unexpander
  | _ => `(<{ ⊤ }>)

@[app_unexpander Ty.bool]
private def Ty.unexpandBool : Unexpander
  | stx => do
      let Bool := mkObjectIdentFrom stx "Bool"
      let T ← `(stlcTy| $Bool:ident)
      `(<{ $T:stlcTy }>)

@[app_unexpander Ty.unit]
private def Ty.unexpandUnit : Unexpander
  | stx => do
      let Unit := mkObjectIdentFrom stx "Unit"
      let T ← `(stlcTy| $Unit:ident)
      `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Ty.prod]
private def Ty.unexpandProd : Unexpander
  | `($_ $T₁ $T₂) => do
      let T₁' := getTy T₁
      let T₂' := getTy T₂
      `(<{ $T₁':stlcTy × $T₂':stlcTy }>)
  | _ => throw ()

private def reservedTyNames : String → Bool
  | "Bool" | "Unit" => true
  | _ => false

@[app_unexpander Ty.base]
private def Ty.unexpandBase : Unexpander
  | stx@`($_ $s:str) => do
      let name := s.getString
      let id := mkObjectIdentFrom stx name
      match classifyIdent? id, reservedTyNames name with
      | some (.object, _), false =>
          let T ← `(stlcTy| $id:ident)
          `(<{ $T:stlcTy }>)
      | _, _ => throw ()
  | _ => throw ()

private def reservedTmNames : String → Bool
  | "true" | "false" | "Bool"
  | "Unit" | "unit" | "fst"
  | "snd" => true
  | _ => false


@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander :=
  Delab.unexpandVar reservedTmNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.tru]
private def Tm.unexpandTru : Unexpander
  | stx => do
      let tru := mkObjectIdentFrom stx "true"
      let t ← `(stlcTm| $tru:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.fls]
private def Tm.unexpandFls : Unexpander
  | stx => do
      let fls := mkObjectIdentFrom stx "false"
      let t ← `(stlcTm| $fls:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.ite]
private def Tm.unexpandIte : Unexpander
  | `($_ $c $t $e) => do
      let c' := getTm c
      let t' := getTm t
      let e' := getTm e
      `(<{if $c':stlcTm then $t':stlcTm else $e':stlcTm }>)
  | _ => throw ()


@[app_unexpander Tm.unit]
private def Tm.unexpandUnit : Unexpander
  | stx => do
      let unit := mkObjectIdentFrom stx "unit"
      let t ← `(stlcTm| $unit:ident)
      `(<{ $t:stlcTm }>)

@[app_unexpander Tm.pair]
private def Tm.unexpandPair : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ ($t₁':stlcTm, $t₂':stlcTm) }>)
  | _ => throw ()


@[app_unexpander Tm.fst]
private def Tm.unexpandFst : Unexpander
  | stx@`($_ $t) => do
      let fst := mkObjectIdentFrom stx "fst"
      let t' := getTm t
      `(<{ $fst:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.snd]
private def Tm.unexpandSnd : Unexpander
  | stx@`($_ $t) => do
      let snd := mkObjectIdentFrom stx "snd"
      let t' := getTm t
      `(<{ $snd:ident $t':stlcTm }>)
  | _ => throw ()

end Delab

/-- info: <{ λ X : Nat . X }> : Tm -/
#guard_msgs in
#check <{ λ X : Nat. X }>

/-- info: <{ if X then X else X }> : Tm -/
#guard_msgs in
#check <{ if X then X else X }>

/-- info: <{ if Y X then X else X }> : Tm -/
#guard_msgs in
#check <{ if Y X then X else X }>

/-- info: <{ if Y X then X else X }> : Tm -/
#guard_msgs in
#check <{ if (Y X) then X else X }>

/-- info: <{ ( X , Y ) }> : Tm -/
#guard_msgs in
#check <{ (X , Y) }>

/-- info: <{ fst X }> : Tm -/
#guard_msgs in
#check <{ fst X }>

/-- info: <{ fst  ( X , Y ) }> : Tm -/
#guard_msgs in
#check <{ fst (X , Y) }>

/--
info: <{ λ X : Bool . λ Y : ⊤ . if X then true else false }> : Tm
---
warning: Variable name `Y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _Y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
#check <{ λ X : Bool . λ Y : ⊤ . if X then true else false }>

/-- info: <{ Unit }> : Ty -/
#guard_msgs in
#check <{ Unit }>

/-- info: <{ A }> : Ty -/
#guard_msgs in
#check (Ty.base "A" : Ty)

/-- info: <{ A → ⊤ }> : Ty -/
#guard_msgs in
#check (<{ A → ⊤ }> : Ty)

/-- info: <{ Unit }> : Ty -/
#guard_msgs in
#check (Ty.unit : Ty)

/-- info: Ty.base "Bool" : Ty -/
#guard_msgs in
#check (Ty.base "Bool" : Ty)

/-- info: <{ Bool }> : Ty -/
#guard_msgs in
#check (Ty.bool: Ty)

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ y : τ . [x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([x := s] t₁) ([x := s] t₂) }>
  -- unit
  | .unit => <{ unit }>
  -- bools
  | .tru => <{ true }>
  | .fls => <{ false }>
  | .ite t₁ t₂ t₃ =>
      <{ if [x := s] t₁ then [x := s] t₂ else [x := s] t₃ }>

  -- Complete the following cases when you do the `products` exercise later
  | .pair t₁ t₂ =>
      (<{ ([x := s] t₁ , [x := s] t₂) }>) -- solution
  | .fst t =>
      (<{ fst ([x := s] t)}>) -- solution
  | .snd t =>
      (<{ snd ([x := s] t)}>) -- solution

open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst

inductive Tm.IsValue : Tm → Prop where
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) :
      IsValue <{λ x : τ₂ . t₁}>
  | tru :
      IsValue <{true}>
  | fls :
      IsValue <{false}>
  | unit :
      IsValue <{unit}>

-- Fill in more rules when you do the `products` exercise later
-- SOLUTION
  | pair (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{(v₁, v₂)}>

-- attribute [StlcSubEval] Tm.IsValue.pair
-- END SOLUTION

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  -- pure STLC
  | appAbs (x : String) (τ₂ : Ty) (t₁ v₂ : Tm) :
      v₂.IsValue →
       <{(λ x : τ₂ . t₁) v₂}> ⟶ <{ [x := v₂] t₁ }>
  | app₁ (t₁ t₁' t₂ : Tm) :
      t₁ ⟶ t₁' →
      <{t₁ t₂}> ⟶ <{t₁' t₂}>
  | app₂ (v₁ t₂ t₂' : Tm) :
      v₁.IsValue →
      t₂ ⟶ t₂' →
      <{v₁ t₂}> ⟶ <{v₁ t₂'}>
  -- booleans
  | ifStep (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if t₁ then t₂ else t₃ }> ⟶ <{ if t₁' then t₂ else t₃ }>
  | ifTrue (t₂ t₃ : Tm) :
      <{ if true then t₂ else t₃ }> ⟶ t₂
  | ifFalse (t₂ t₃ : Tm) :
      <{ if false then t₂ else t₃ }> ⟶ t₃

  -- Fill in more rules when you do the `products` exercise later
  -- SOLUTION
  | pair₁  (t₁ t₁' t₂ : Tm) :
      t₁ ⟶ t₁' →
      <{ (t₁, t₂) }> ⟶ <{ (t₁', t₂) }>
  | pair₂ (v₁ t₂ t₂' : Tm) :
      v₁.IsValue →
      t₂ ⟶ t₂' →
      <{ (v₁, t₂) }> ⟶  <{ (v₁, t₂') }>
  | fst₁ (t t' : Tm) :
      t ⟶ t' →
      <{ fst t }> ⟶ <{ fst t' }>
  | fstPair (v₁ v₂ : Tm) :
      v₁.IsValue →
      v₂.IsValue →
      <{ fst (v₁ , v₂) }> ⟶ v₁
  | snd₁ (t t' : Tm) :
      t ⟶ t' →
      <{ snd t }> ⟶ <{ snd t' }>
  | sndPair (v₁ v₂ : Tm) :
      v₁.IsValue →
      v₂.IsValue →
      <{ snd (v₁, v₂) }> ⟶ v₂
  -- END SOLUTION
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

section
set_option hygiene false in
local notation:40 τ:41 " <: " τ':41 => Subtype τ τ'

inductive Subtype : Ty → Ty → Prop where
  | refl {τ : Ty} :
      τ <: τ
  | trans {σ υ τ: Ty}
      (h₁ : σ <: υ)
      (h₂ : υ <: τ) :
      σ <: τ
  | top {σ : Ty} :
      σ <: <{ ⊤ }>
  | arrow { σ₁ σ₂ τ₁ τ₂ : Ty}
      (h₁ : τ₁ <: σ₁)
      (h₂ : σ₂ <: τ₂) :
      <{ σ₁ → σ₂ }> <: <{ τ₁ → τ₂ }>

-- Fill in more rules when you do the `products` exercise later
-- SOLUTION
  | prod { σ₁ σ₂ τ₁ τ₂ : Ty}
      (h₁ : σ₁ <: τ₁)
      (h₂ : σ₂ <: τ₂) :
      <{ σ₁ × σ₂ }> <: <{ τ₁ × τ₂ }>
-- END SOLUTION
end

scoped notation:40 τ:41 " <: " τ':41 => Subtype τ τ'

abbrev Context := PartialMap String Ty

inductive HasType : Context → Tm → Ty → Prop where
  -- pure STLC
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      <{ Γ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ ⊢ λ x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ τ₂ → τ₁ }>) (h₂ : <{ Γ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ ⊢ t₁ t₂ ⦂ τ₁ }>
  -- booleans
  | tru (Γ : Context) :
      <{ Γ ⊢ true ⦂ Bool }>
  | fls (Γ : Context) :
      <{ Γ ⊢ false ⦂ Bool }>
  | ite (Γ : Context) (t₁ t₂ t₃ : Tm) (τ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Bool }>) (h₂ : <{ Γ ⊢ t₂ ⦂ τ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ τ }>) :
      <{ Γ ⊢ if t₁ then t₂ else t₃ ⦂ τ }>
  -- unit
  | unit (Γ : Context) :
      <{ Γ ⊢ unit ⦂ Unit }>
  -- subsumption
  | sub (Γ : Context) (t₁ : Tm) (τ₁ τ₂ : Ty)
      (ht : <{ Γ ⊢ t₁ ⦂ τ₁ }>)
      (hs : τ₁ <: τ₂) :
      <{ Γ ⊢ t₁ ⦂ τ₂ }>

  -- Fill in more rules when you do the `products` exercise later
  -- SOLUTION
  | pair (Γ : Context) (t₁ t₂ : Tm) (τ₁ τ₂ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ τ₁ }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ ⊢ (t₁, t₂) ⦂ τ₁ × τ₂ }>
  | fst (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty)
      (h : <{ Γ ⊢ t ⦂ τ₁ × τ₂ }>) :
      <{ Γ ⊢ fst t ⦂ τ₁ }>
  | snd (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty)
      (h : <{ Γ ⊢ t ⦂ τ₁ × τ₂ }>) :
      <{ Γ ⊢ snd t ⦂ τ₂ }>
  -- END SOLUTION

open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander := StlcCommon.Delab.unexpandHasType

example : <{ ∅ ⊢ (λ X : (⊤ × (B → B)) . snd X) ((λ Z : A . Z), (λ Z : B . Z)) ⦂ (B → B) }> := by
  apply HasType.app
  · apply HasType.abs
    apply HasType.snd
    apply HasType.var
    rfl
  · apply HasType.pair
    · apply HasType.sub
      · apply HasType.abs
        apply HasType.var
        rfl
      · apply Subtype.top
    · apply HasType.abs
      apply HasType.var
      rfl

end StlcSub
