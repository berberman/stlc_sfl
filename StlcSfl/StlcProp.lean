import StlcSfl.StlcCommon

namespace StlcArith


inductive Ty where
  | arrow (T₁ T₂ : Ty)
  | nat

inductive Tm where
  | var (x : String)
  | app (t₁ t₂ : Tm)
  | abs (x : String) (T : Ty) (t : Tm)
  | const (n : Nat)
  | succ (t : Tm)
  | pred (t : Tm)
  | mult (t₁ t₂ : Tm)
  | ite0 (c t e : Tm)

scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:61 " * " stlcTm:60 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm


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
  subst := `StlcArith.subst
  hasType := `StlcArith.HasType

def natTyHandler : TyElabHandler :=
  fun _recur k T => do
    match T with
    | `(stlcTy| Nat) =>
        return mkConst ``Ty.nat
    | _ => k T

def tyHandlers : TyElabHandler :=
  natTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy unsupportedTy

def arithTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| $n:num) => do
        return (mkApp (mkConst ``Tm.const) (mkNatLit n.getNat), free)
    | `(stlcTm| Nat) => do
        throwError "`Nat` is not a valid term."
    | `(stlcTm| succ $e:stlcTm) => do
        let (e, free) ←  recur Γ free e
        return (mkApp (mkConst ``Tm.succ) e, free)
    | `(stlcTm| pred $e:stlcTm) => do
        let (e, free) ←  recur Γ free e
        return (mkApp (mkConst ``Tm.pred) e, free)
    | `(stlcTm| $t₁:stlcTm * $t₂:stlcTm) => do
        let (e₁, free) ←  recur Γ free t₁
        let (e₂, free) ←  recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.mult) e₁ e₂, free)
    | `(stlcTm| if0 $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite0) c t e, free)
    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  arithTmHandler.orElse (commonTmHandler language elabTy)

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

open StlcCommon Elab Delab
open Lean PrettyPrinter Delaborator

@[app_unexpander Ty.nat]
private def Ty.unexpandNat : Unexpander
  | stx => do
    let T ← `(stlcTy| $(mkIdentFrom stx `Nat):ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

private def reservedNames : String → Bool
  | "Nat" | "succ" | "pred" | "if0" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var

@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var

@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp

@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.ite0]
private def Tm.unexpandIte : Unexpander
  | `($_ $c $t $e) =>
      `(<{ if0 $(getTm c) then $(getTm t) else $(getTm e) }>)
  | _ => throw ()

@[app_unexpander Tm.const]
def Tm.unexpandConst : Unexpander
  | `($_ $n:num) => `(<{ $n:num }>)
  | _ => throw ()

@[app_unexpander Tm.succ]
def Tm.unexpandSucc : Unexpander
  | stx@`($_ $t) => do
    let succ := mkObjectIdentFrom stx "succ"
    `(<{ $succ:ident $(getTm t) }>)
  | _ => throw ()

@[app_unexpander Tm.pred]
def Tm.unexpandPred : Unexpander
  | stx@`($_ $t) => do
    let pred := mkObjectIdentFrom stx "pred"
    `(<{ $pred:ident $(getTm t) }>)
  | _ => throw ()

@[app_unexpander Tm.mult]
def Tm.unexpandMult : Unexpander
  | `($_ $t₁ $t₂) => `(<{ $(getTm t₁) * $(getTm t₂) }>)
  | _ => throw ()

end Delab


/-- info: <{ Nat }> : Ty -/
#guard_msgs in
#check <{ Nat }>

/-- info: <{ λ x : Nat . x }> : Tm -/
#guard_msgs in
#check <{ λ x : Nat . x }>

/-- info: <{ if0 x then x else x }> : Tm -/
#guard_msgs in
#check <{ if0 x then x else x }>

/-- info: <{ if0 y x then x else x }> : Tm -/
#guard_msgs in
#check <{ if0 y x then x else x }>

/-- info: <{ if0 y x then x else x }> : Tm -/
#guard_msgs in
#check <{ if0 (y x) then x else x }>

/-- info: <{ x * y * z }> : Tm -/
#guard_msgs in
#check <{ x * y * z }>

/-- info: <{ succ (pred x) }> : Tm -/
#guard_msgs in
#check <{ succ (pred x) }>

/-- info: <{ succ x y }> : Tm -/
#guard_msgs in
#check <{ succ x y }>

/-- info: <{ x (succ y) }> : Tm -/
#guard_msgs in
#check <{ x (succ y) }>

/-- info: <{ x * y z }> : Tm -/
#guard_msgs in
#check <{ x * y z }>

/-- info: <{ x * y (succ z) }> : Tm -/
#guard_msgs in
#check <{ x * y (succ z) }>

/-- info: <{ z x y }> : Tm -/
#guard_msgs in
#check <{ z x y }>

/-- info: <{ z x * y }> : Tm -/
#guard_msgs in
#check <{ z x * y }>

/-- info: <{ λ x : Nat . λ y : Nat . if0 x then 0 else pred (x * y) }> : Tm -/
#guard_msgs in
#check <{ λ x : Nat . λ y : Nat . if0 x then 0 else pred (x * y) }>

/-- info: <{ «if» }> : Tm -/
#guard_msgs in
#check Tm.var "if"

/-- info: StlcArith.Tm.var "succ" : Tm -/
#guard_msgs in
#check Tm.var "succ"


/-- info: StlcArith.Tm.var "x-y" : Tm -/
#guard_msgs in
#check Tm.var "x-y"

/-- info: StlcArith.Tm.var "1x" : Tm -/
#guard_msgs in
#check Tm.var "1x"

/-- info: StlcArith.Tm.var "_" : Tm -/
#guard_msgs in
#check Tm.var "_"

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  | .var y =>
      if x = y then s else t
  | .abs y T t₁ =>
      if x = y then t else <{ λ ~y : T . [~x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([~x := s] t₁) ([~x := s] t₂) }>
  | .const _ =>
      t
  | .succ t₁ =>
      <{ succ ([~x := s] t₁) }>
  | .pred t₁ =>
      <{ pred ([~x := s] t₁) }>
  | .mult t₁ t₂ =>
      <{ ([~x := ~s] t₁) * ([~x := s] t₂) }>
  | .ite0 t₁ t₂ t₃ =>
      <{ if0 [~x := s] t₁ then [~x := s] t₂ else [~x := s] t₃ }>


open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst

section
variable (x y : String) (s t t₁ t₂ t₃ : Tm) (T : Ty) (n : Nat)

@[simp] theorem subst_var_eq : <{ [~x := s] ~(Tm.var x) }> = s := by
  simp [subst]

@[simp] theorem subst_var_ne (h : x ≠ y) : <{ [~x := s] ~(Tm.var y) }> = .var y := by
  simp [subst, h]

@[simp] theorem subst_abs_eq : <{ [~x := s] (λ ~x : T . t) }> = <{ λ ~x : T . t }> := by
  simp [subst]

@[simp] theorem subst_abs_ne (h : x ≠ y) :
    <{ [~x := s] (λ ~y : T . t) }> = <{ λ ~y : ~T . [~x := s] t }> := by
  simp [subst, h]

@[simp] theorem subst_app :
    <{ [~x := s] (t₁ t₂) }> = <{ ([~x := s] t₁) ([~x := s] t₂) }> := rfl

@[simp] theorem subst_const : <{ [~x := ~s] ~(Tm.const n) }> = .const n := rfl

@[simp] theorem subst_succ :
    <{ [~x := s] (succ t₁) }> = <{ succ ([~x := s] t₁) }> := rfl

@[simp] theorem subst_pred :
    <{ [~x := s] (pred t₁) }> = <{ pred ([~x := s] t₁) }> := rfl

@[simp] theorem subst_mult :
    <{ [~x := s] (t₁ * t₂) }> = <{ ([~x := s] ~t₁) * ([~x := s] t₂) }> := rfl

@[simp] theorem subst_ite0 :
    <{ [~x := s] (if0 t₁ then t₂ else t₃) }> =
      <{ if0 [~x := s] t₁ then [~x := s] t₂ else [~x := s] t₃ }> := rfl
-- END SOLUTION
end

inductive Tm.IsValue : Tm → Prop where
-- SOLUTION
  | abs (x : String) (T₂ : Ty) (t₁ : Tm) : Tm.IsValue <{ λ ~x : T₂ . t₁ }>
  | const (n : Nat) : Tm.IsValue (.const n)
-- END SOLUTION

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
-- SOLUTION
  | appAbs (x : String) (T : Ty) (t v : Tm) (hv : v.IsValue) :
      <{ (λ ~x : T . t) v }> ⟶ <{ [~x := v] t }>
  | app1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ t₁ t₂ }> ⟶ <{ t₁' t₂ }>
  | app2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ v₁ t₂ }> ⟶ <{ v₁ t₂' }>
  | succ (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') :
      <{ succ t₁ }> ⟶ <{ succ t₁' }>
  | succConst (n : Nat) :
      <{ succ ~(Tm.const n) }> ⟶ Tm.const (1 + n)
  | pred (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') :
      <{ pred t₁ }> ⟶ <{ pred t₁' }>
  | predConst (n : Nat) :
      <{ pred ~(Tm.const n) }> ⟶ Tm.const (n - 1)
  | multConst (n₁ n₂ : Nat) :
      <{ ~(Tm.const n₁) * ~(Tm.const n₂) }> ⟶ Tm.const (n₁ * n₂)
  | mult1 (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ t₁ * t₂ }> ⟶ <{ t₁' * t₂ }>
  | mult2 (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ v₁ * t₂ }> ⟶ <{ v₁ * t₂' }>
  | if0Step (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if0 t₁ then t₂ else t₃ }> ⟶ <{ if0 t₁' then t₂ else t₃ }>
  | if0Zero (t₂ t₃ : Tm) :
      <{ if0 0 then t₂ else t₃ }> ⟶ t₂
  | if0Nonzero (n : Nat) (t₂ t₃ : Tm) :
      <{ if0 ~(Tm.const (n + 1)) then ~t₂ else ~t₃ }> ⟶ t₃
-- END SOLUTION
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

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

  | const (Γ : Context) (n : Nat) :
      <{ Γ ⊢ ~(Tm.const n) ⦂ Nat }>

  | succ (Γ : Context) (t₁ : Tm)
      (h : <{ Γ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ ⊢ succ t₁ ⦂ Nat }>

  | pred (Γ : Context) (t₁ : Tm)
      (h : <{ Γ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ ⊢ pred t₁ ⦂ Nat }>

  | mult (Γ : Context) (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Nat }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ Nat }>) :
      <{ Γ ⊢ t₁ * t₂ ⦂ Nat }>

  | ite0 (Γ : Context) (t₁ t₂ t₃ : Tm) (T₀ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Nat }>)
      (h₂ : <{ Γ ⊢ t₂ ⦂ T₀ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ T₀ }>) :
      <{ Γ ⊢ if0 t₁ then t₂ else t₃ ⦂ T₀ }>

end StlcArith
