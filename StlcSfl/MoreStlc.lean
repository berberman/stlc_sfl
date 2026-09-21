import StlcSfl.StlcCommon

namespace StlcExtended

inductive Ty : Type where
  | arrow : Ty → Ty → Ty
  | nat  : Ty
  | sum  : Ty → Ty → Ty
  | list : Ty → Ty
  | unit : Ty
  | prod : Ty → Ty → Ty


inductive Tm : Type where
  -- pure STLC
  | var : String → Tm
  | app : Tm → Tm → Tm
  | abs : String → Ty → Tm → Tm
  -- numbers
  | const: Nat → Tm
  | succ : Tm → Tm
  | pred : Tm → Tm
  | mult : Tm → Tm → Tm
  | ite0  : Tm → Tm → Tm → Tm
  -- sums
  | sumInl : Ty → Tm → Tm
  | sumInr : Ty → Tm → Tm
  | sumCase : Tm → String → Tm → String → Tm → Tm
          -- i.e., `case t of inl x₁ => t₁ | inr x₂ => t₂`
  -- lists
  | listNil : Ty → Tm
  | listCons : Tm → Tm → Tm
  | listCase : Tm → Tm → String → String → Tm → Tm
          -- i.e., [case t₁ of | nil => t₂ | x::y => t₃]
  -- unit
  | unit : Tm

  -- pairs
  | pair : Tm → Tm → Tm
  | fst : Tm → Tm
  | snd : Tm → Tm
  -- let
  | letIn : String → Tm → Tm → Tm
         -- i.e., [let x = t₁ in t₂]
  -- fix
  | fix  : Tm → Tm

scoped syntax:50 stlcTy:51 " × " stlcTy:50 : stlcTy
scoped syntax:50 stlcTy:51 " + " stlcTy:50 : stlcTy
scoped syntax:51 " [ " stlcTy:50  " ] " : stlcTy

scoped syntax:max num : stlcTm
scoped syntax:60 stlcTm:61 " * " stlcTm:60 : stlcTm
scoped syntax:50 "if0 " stlcTm:51 " then " stlcTm:50 " else " stlcTm:50 : stlcTm

scoped syntax:60 " inr " stlcTy:60 ppSpace stlcTm:60 : stlcTm
scoped syntax:60 " inl " stlcTy:60 ppSpace stlcTm:60 : stlcTm
scoped syntax:50 "case " stlcTm:50 " of " "inl" stlcVar " => " stlcTm:50 " | "
  "inr" stlcVar " => " stlcTm:50 : stlcTm

scoped syntax:60 " nil " stlcTy:60 : stlcTm
scoped syntax:60 stlcTm:61 " :: " stlcTm:60 : stlcTm
scoped syntax:50 "case " stlcTm:50 " of " "nil" " => " stlcTm:50 " | "
  stlcVar " :: " stlcVar " => " stlcTm:50 : stlcTm

scoped syntax:max " ( " stlcTm:60 " , " stlcTm:60 " ) " : stlcTm

scoped syntax:50 "let " stlcVar " = " stlcTm:50 " in " stlcTm:50 : stlcTm

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
  subst := `StlcExtended.subst
  hasType := `StlcExtended.HasType

def extendedTyHandler : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| Nat) =>
        return mkConst ``Ty.nat
    | `(stlcTy| Unit) =>
        return mkConst ``Ty.unit
    | `(stlcTy| $T₁:stlcTy + $T₂:stlcTy) => do
        let T₁ ← recur T₁
        let T₂ ← recur T₂
        return mkApp2 (mkConst ``Ty.sum) T₁ T₂
    | `(stlcTy| [$T:stlcTy]) => do
        let T ← recur T
        return mkApp (mkConst ``Ty.list) T
    | `(stlcTy| $T₁:stlcTy × $T₂:stlcTy) => do
        let T₁ ← recur T₁
        let T₂ ← recur T₂
        return mkApp2 (mkConst ``Ty.prod) T₁ T₂
    | _ => k T

def tyHandlers : TyElabHandler :=
  extendedTyHandler.orElse (commonTyHandler language)

partial def elabTy : TyElab :=
  tyHandlers elabTy unsupportedTy

def extendedTmHandler : TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    | `(stlcTm| $n:num) => do
        return (mkApp (mkConst ``Tm.const) (mkNatLit n.getNat), free )

    | `(stlcTm| Nat) => do
        throwError "`Nat` is not a valid term."

    | `(stlcTm| succ $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.succ) t, free)

    | `(stlcTm| pred $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.pred) t, free)

    | `(stlcTm| $t₁:stlcTm * $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.mult) t₁ t₂, free)

    | `(stlcTm| if0 $c:stlcTm then $t:stlcTm else $e:stlcTm) => do
        let (c, free) ← recur Γ free c
        let (t, free) ← recur Γ free t
        let (e, free) ← recur Γ free e
        return (mkApp3 (mkConst ``Tm.ite0) c t e, free)

    | `(stlcTm| inl $T:stlcTy $t:stlcTm) => do
        let T ← elabTy T
        let (t, free) ← recur Γ free t
        return (mkApp2 (mkConst ``Tm.sumInl) T t, free)

    | `(stlcTm| inr $T:stlcTy $t:stlcTm) => do
        let T ← elabTy T
        let (t, free) ← recur Γ free t
        return (mkApp2 (mkConst ``Tm.sumInr) T t, free)

    | `(stlcTm|
        case $t:stlcTm of
          inl $x₁:stlcVar => $t₁:stlcTm |
          inr $x₂:stlcVar => $t₂:stlcTm) => do

        let (t, free) ← recur Γ free t

        -- The branches start from the same lexical Γ
        -- Only `free` is threaded from branch 1 into branch 2
        let (x₁, Γ₁) ← elabStlcBinder language Γ x₁
        let (t₁, free) ← recur Γ₁ free t₁

        let (x₂, Γ₂) ← elabStlcBinder language Γ x₂
        let (t₂, free) ← recur Γ₂ free t₂

        return (mkAppN (mkConst ``Tm.sumCase) #[t, x₁, t₁, x₂, t₂], free)

    | `(stlcTm| nil $T:stlcTy) => do
        let T ← elabTy T
        return (mkApp (mkConst ``Tm.listNil) T, free)

    | `(stlcTm| $t₁:stlcTm :: $t₂:stlcTm) => do
        let (t₁, free) ← recur Γ free t₁
        let (t₂, free) ← recur Γ free t₂
        return (mkApp2 (mkConst ``Tm.listCons) t₁ t₂,  free)

    | `(stlcTm|
        case $t₁:stlcTm of
          nil => $t₂:stlcTm |
          $x:stlcVar :: $xs:stlcVar => $t₃:stlcTm) => do

        let (t₁, free) ← recur Γ free t₁

        -- nil branch has no binders
        let (t₂, free) ← recur Γ free t₂

        -- cons branch has two binders
        let (x, Γ) ← elabStlcBinder language Γ x
        let (xs, Γ) ← elabStlcBinder language Γ xs

        let (t₃, free) ← recur Γ free t₃

        return (mkAppN (mkConst ``Tm.listCase) #[t₁, t₂, x, xs, t₃], free)

    | `(stlcTm| Unit) => do
        throwError "`Unit` is not a valid term."

    | `(stlcTm| unit) => do
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

    | `(stlcTm|
        let $x:stlcVar = $t₁:stlcTm
        in $t₂:stlcTm) => do

        -- x is NOT in scope in t₁
        let (t₁, free) ← recur Γ free t₁

        -- but in scope in t₂
        let (x, Γ₂) ← elabStlcBinder language Γ x

        let (t₂, free) ← recur Γ₂ free t₂

        return (mkApp3 (mkConst ``Tm.letIn) x t₁ t₂, free)

    | `(stlcTm| fix $t:stlcTm) => do
        let (t, free) ← recur Γ free t
        return (mkApp (mkConst ``Tm.fix) t, free)

    | _ => k Γ free t

def tmHandlers : TmElabHandler :=
  extendedTmHandler.orElse (commonTmHandler language elabTy)


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
    let Nat := mkObjectIdentFrom stx "Nat"
    let T ← `(stlcTy| $Nat:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.unit]
private def Ty.unexpandUnit : Unexpander
  | stx => do
    let Unit := mkObjectIdentFrom stx "Unit"
    let T ← `(stlcTy| $Unit:ident)
    `(<{ $T:stlcTy }>)

@[app_unexpander Ty.arrow]
private def Ty.unexpandArrow : Unexpander := Delab.unexpandArrow

@[app_unexpander Ty.sum]
private def Ty.unexpandSum : Unexpander
  | `($_ $T₁ $T₂) => do
      let T₁' := getTy T₁
      let T₂' := getTy T₂
      `(<{ $T₁':stlcTy + $T₂':stlcTy }>)
  | _ => throw ()


@[app_unexpander Ty.list]
private def Ty.unexpandList : Unexpander
  | `($_ $T) => do
      let T' := getTy T
      `(<{ [$T':stlcTy] }>)
  | _ => throw ()

@[app_unexpander Ty.prod]
private def Ty.unexpandProd : Unexpander
  | `($_ $T₁ $T₂) => do
      let T₁' := getTy T₁
      let T₂' := getTy T₂
      `(<{ $T₁':stlcTy × $T₂':stlcTy }>)
  | _ => throw ()

private def reservedNames : String → Bool
  | "Nat" | "Unit" | "succ" | "pred"
  | "if0" | "inl" | "inr" | "nil"
  | "unit" | "fst" | "snd" | "let"
  | "fix" | "case" => true
  | _ => false

@[app_unexpander Tm.var]
private def Tm.unexpandVar : Unexpander := Delab.unexpandVar reservedNames ``Tm.var


@[app_delab Tm.var]
private def Tm.delabVar : Delab := Delab.delabVar ``Tm.var


@[app_unexpander Tm.app]
private def Tm.unexpandApp : Unexpander := Delab.unexpandApp


@[app_unexpander Tm.abs]
private def Tm.unexpandAbs : Unexpander := Delab.unexpandAbs

@[app_unexpander Tm.const]
private def Tm.unexpandConst : Unexpander
  | `($_ $n:num) => `(<{ $n:num }>)
  | _ => throw ()

@[app_unexpander Tm.succ]
private def Tm.unexpandSucc : Unexpander
  | stx@`($_ $t) => do
      let succ := mkObjectIdentFrom stx "succ"
      let t' := getTm t
      `(<{ $succ:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.pred]
private def Tm.unexpandPred : Unexpander
  | stx@`($_ $t) => do
      let pred := mkObjectIdentFrom stx "pred"
      let t' := getTm t
      `(<{ $pred:ident $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.mult]
private def Tm.unexpandMult : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm * $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.ite0]
private def Tm.unexpandIte0 : Unexpander
  | `($_ $c $t $e) => do
      let c' := getTm c
      let t' := getTm t
      let e' := getTm e
      `(<{ if0 $c':stlcTm then $t':stlcTm else $e':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.sumInl]
private def Tm.unexpandSumInl : Unexpander
  | `($_ $T $t) => do
      let T' := getTy T
      let t' := getTm t
      `(<{ inl $T':stlcTy $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.sumInr]
private def Tm.unexpandSumInr : Unexpander
  | `($_ $T $t) => do
      let T' := getTy T
      let t' := getTm t
      `(<{ inr $T':stlcTy $t':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.sumCase]
private def Tm.unexpandSumCase : Unexpander
  | `($_ $t $x₁ $t₁ $x₂ $t₂) => do
      let t' := getTm t
      let x₁' := getVar x₁
      let t₁' := getTm t₁
      let x₂' := getVar x₂
      let t₂' := getTm t₂

      `(<{
        case $t':stlcTm of
          inl $x₁':stlcVar => $t₁':stlcTm |
          inr $x₂':stlcVar => $t₂':stlcTm
      }>)
  | _ => throw ()


@[app_unexpander Tm.listNil]
private def Tm.unexpandListNil : Unexpander
  | `($_ $T) => do
      let T' := getTy T
      `(<{ nil $T':stlcTy }>)
  | _ => throw ()

@[app_unexpander Tm.listCons]
private def Tm.unexpandListCons : Unexpander
  | `($_ $t₁ $t₂) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{ $t₁':stlcTm :: $t₂':stlcTm }>)
  | _ => throw ()

@[app_unexpander Tm.listCase]
private def Tm.unexpandListCase : Unexpander
  | `($_ $t₁ $t₂ $x $xs $t₃) => do
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      let x' := getVar x
      let xs' := getVar xs
      let t₃' := getTm t₃
      `(<{
        case $t₁':stlcTm of
          nil => $t₂':stlcTm |
          $x':stlcVar :: $xs':stlcVar => $t₃':stlcTm
      }>)
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
  | _ =>
      throw ()

@[app_unexpander Tm.letIn]
private def Tm.unexpandLetIn : Unexpander
  | `($_ $x $t₁ $t₂) => do
      let x' := getVar x
      let t₁' := getTm t₁
      let t₂' := getTm t₂
      `(<{
        let $x':stlcVar =
          $t₁':stlcTm
        in
          $t₂':stlcTm
      }>)
  | _ => throw ()


@[app_unexpander Tm.fix]
private def Tm.unexpandFix : Unexpander
  | stx@`($_ $t) => do
      let fix := mkObjectIdentFrom stx "fix"
      let t' := getTm t
      `(<{ $fix:ident $t':stlcTm }>)
  | _ => throw ()

end Delab

/-- info: <{ unit }> : Tm -/
#guard_msgs in
#check <{ unit }>

/-- info: <{ Nat }> : Ty -/
#guard_msgs in
#check (Ty.nat : Ty)

/-- info: <{ Unit }> : Ty -/
#guard_msgs in
#check (Ty.unit : Ty)

/-- info: <{ unit }> : Tm -/
#guard_msgs in
#check (Tm.unit : Tm)

/-- info: <{ 0 }> : Tm -/
#guard_msgs in
#check (Tm.const 0 : Tm)

example (x : Tm) : (<{ x }> : Tm) = x := rfl

/-- info: <{ λ x : Nat . x }> : Tm -/
#guard_msgs in
#check <{ λx : Nat. x }>

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

/-- info: <{ inr Nat (λ x : Unit . x) }> : Tm -/
#guard_msgs in
#check <{ inr Nat (λx : Unit . x) }>

/-- info: <{ nil Nat }> : Tm -/
#guard_msgs in
#check <{ nil Nat }>

/-- info: <{ 3 :: nil Nat }> : Tm -/
#guard_msgs in
#check <{ 3 :: nil Nat }>

/-- info: <{ ( x , y ) }> : Tm -/
#guard_msgs in
#check <{ (x , y) }>

/-- info: <{ fst x }> : Tm -/
#guard_msgs in
#check <{ fst x }>

/-- info: <{ fst  ( x , y ) }> : Tm -/
#guard_msgs in
#check <{ fst (x , y) }>

/-- info: <{ inl Nat 3 }> : Tm -/
#guard_msgs in
#check <{ inl Nat 3 }>

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

/-- info: <{ ( [ Nat ] → Nat × Unit) → Nat + Unit }> : Ty -/
#guard_msgs in
#check <{ ([Nat] -> Nat × Unit) -> Nat + Unit }>

/-- info: <{ let x = 1 in ( x , unit ) }> : Tm -/
#guard_msgs in
#check <{ let x = 1 in (x, unit) }>

/-- info: (Ty.nat.list.arrow (Ty.nat.prod Ty.unit)).arrow (Ty.nat.sum Ty.unit) : Ty -/
#guard_msgs in
set_option pp.notation false in
#check <{ ([Nat] -> Nat × Unit) -> Nat + Unit }>

example :
    (<{ case s of inl x => x | inr y => y }> : Tm) =
      Tm.sumCase
        (Tm.var "s")
        "x" (Tm.var "x")
        "y" (Tm.var "y") := rfl

example :
    (<{
      case xs of
        nil => z |
        x :: xs => x
    }> : Tm) =
      Tm.listCase
        (Tm.var "xs")
        (Tm.var "z")
        "x"
        "xs"
        (Tm.var "x") := rfl

example :
    (<{ let x = y in x }> : Tm) =
      Tm.letIn
        "x"
        (Tm.var "y")
        (Tm.var "x") := rfl

def subst (x : String) (s : Tm) (t : Tm) : Tm :=
  match t with
  -- pure STLC
  | .var y =>
      if x = y then s else t
  | .abs y τ t₁ =>
      if x = y then t else <{ λ ~y : τ . [~x := s] t₁ }>
  | .app t₁ t₂ =>
      <{ ([~x := s] t₁) ([~x := s] t₂) }>
  -- numbers
  | .const _ =>
      t
  | .succ t₁ =>
      <{ succ ([~x := s] t₁) }>
  | .pred t₁ =>
      <{ pred ([~x := s] t₁) }>
  | .mult t₁ t₂ =>
      <{ ([~x := s] t₁) * ([~x := s] t₂) }>
  | .ite0 t₁ t₂ t₃ =>
      <{
        if0 [~x := s] t₁
        then [~x := s] t₂
        else [~x := s] t₃
      }>
  -- sums
  | .sumInl τ₂ t₁ =>
      <{ inl τ₂ ([~x := s] t₁) }>
  | .sumInr τ₂ t₁ =>
      <{ inr τ₂ ([~x := s] t₁) }>
  | .sumCase t x₁ t₁ x₂ t₂ =>
      let t₁ := if x = x₁ then t₁ else <{ [~x := s] t₁ }>
      let t₂ := if x = x₂ then t₂ else <{ [~x := s] t₂ }>
      <{
        case ([~x := s] t) of
          inl ~x₁ => t₁ |
          inr ~x₂ => t₂
      }>
  -- lists
  | .listNil _ => t
  | .listCons t₁ t₂ => <{ ([~x := s] t₁) :: ([~x := s] t₂) }>
  | .listCase t₁ t₂ x₁ x₂ t₃ =>
      let t₃ := if x = x₁ || x = x₂ then t₃ else <{ [~x := s] t₃ }>
      <{
        case ([~x := s] t₁) of
          nil => [~x := s] t₂ |
          ~x₁ :: ~x₂ => t₃
      }>
  -- unit
  | .unit => <{ unit }>
  -- pairs
  | .pair t₁ t₂ =>
      <{ (([~x := s] t₁), ([~x := s] t₂)) }>
  | .fst t₁ =>
      <{ fst ([~x := s] t₁) }>
  | .snd t₁ =>
      <{ snd ([~x := s] t₁) }>
  -- let
  | .letIn y t₁ t₂ =>
      let t₂ := if x = y then t₂ else <{ [~x := s] t₂ }>
      <{
        let ~y = [~x := s] t₁ in t₂
      }>
  -- fix
  | .fix t₁ => <{ fix ([~x := s] t₁) }>

open Lean PrettyPrinter in
@[app_unexpander subst]
def unexpandSubst : Unexpander := StlcCommon.Delab.unexpandSubst

inductive Tm.IsValue : Tm → Prop where
  -- In pure STLC, function abstractions are values:
  | abs (x : String) (τ₂ : Ty) (t₁ : Tm) : IsValue <{λ ~x : τ₂ . t₁}>
  -- Numbers are values:
  | nat (n : Nat) : IsValue (.const n)
  -- A tagged value is a value:
  | sumInl (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inl τ₁ v}>
  | sumInr  (v : Tm) (τ₁ : Ty) :
      IsValue v →
      IsValue <{inr τ₁ v}>
  -- A list is a value iff its head and tail are values:
  | listNil (τ₁ : Ty) : IsValue <{nil τ₁}>
  | listCons (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{v₁ :: v₂}>
  -- A unit is always a value
  | unit : IsValue <{unit}>
  -- A pair is a value if both components are:
  | pair (v₁ v₂ : Tm) :
      IsValue v₁ →
      IsValue v₂ →
      IsValue <{(v₁, v₂)}>

section
set_option hygiene false in
local notation:40 t:41 " ⟶ " t':41 => Step t t'

inductive Step : Tm → Tm → Prop where
  -- pure STLC
  | appAbs (x : String) (τ₂ : Ty) (t₁ v₂ : Tm) :
      v₂.IsValue →
      <{(λ ~x: τ₂ . t₁) v₂}> ⟶ <{ [~x := v₂] t₁ }>
  | app₁ (t₁ t₁' t₂ : Tm) :
      t₁ ⟶ t₁' →
      <{t₁ t₂}> ⟶ <{t₁' t₂}>
  | app₂ (v₁ t₂ t₂' : Tm) :
      v₁.IsValue →
      t₂ ⟶ t₂' →
      <{v₁ t₂}> ⟶ <{v₁  t₂'}>
  -- numbers
  | succ (t₁ t₁' : Tm) :
      t₁ ⟶ t₁' →
      <{succ t₁}> ⟶ <{succ t₁'}>
  | succNat (n : Nat) :
      <{ succ ~(Tm.const n) }> ⟶ Tm.const (n + 1)
  | pred (t₁ t₁' : Tm) (h : t₁ ⟶ t₁') :
      <{ pred t₁ }> ⟶ <{ pred t₁' }>
  | predConst (n : Nat) :
      <{ pred ~(Tm.const n) }> ⟶ Tm.const (n - 1)
  | multConst (n₁ n₂ : Nat) :
      <{ ~(Tm.const n₁) * ~(Tm.const n₂) }> ⟶ Tm.const (n₁ * n₂)
  | mult₁ (t₁ t₁' t₂ : Tm) (h : t₁ ⟶ t₁') :
      <{ t₁ * t₂ }> ⟶ <{ t₁' * t₂ }>
  | mult₂ (v₁ t₂ t₂' : Tm) (hv : v₁.IsValue) (h : t₂ ⟶ t₂') :
      <{ v₁ * t₂ }> ⟶ <{ v₁ * t₂' }>
  | if0Step (t₁ t₁' t₂ t₃ : Tm) (h : t₁ ⟶ t₁') :
      <{ if0 t₁ then t₂ else t₃ }> ⟶ <{ if0 t₁' then t₂ else t₃ }>
  | if0Zero (t₂ t₃ : Tm) :
      <{ if0 0 then t₂ else t₃ }> ⟶ t₂
  | if0Nonzero (n : Nat) (t₂ t₃ : Tm) :
      <{ if0 ~(Tm.const (n + 1)) then t₂ else t₃ }> ⟶ t₃
  -- sums
  | sumInl (t₁ t₁' : Tm) (τ₂ : Ty) :
      t₁ ⟶ t₁' →
      <{inl τ₂ t₁}> ⟶ <{inl τ₂ t₁'}>
  | sumInr (t₂ t₂' : Tm) (τ₁ : Ty) :
      t₂ ⟶ t₂' →
      <{inr τ₁ t₂}> ⟶ <{inr τ₁ t₂'}>
  | sumCase (t t' : Tm) (x₁ : String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) :
      t ⟶ t' →
      <{case t of inl ~x₁ => t₁ | inr ~x₂ => t₂}> ⟶
      <{case t' of inl ~x₁ => t₁ | inr ~x₂ => t₂}>
  | sumCaseInl (v : Tm) (x₁:String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) (τ₂ : Ty) :
      v.IsValue →
      <{case inl τ₂ v of inl ~x₁ => t₁ | inr ~x₂ => t₂}> ⟶ <{ [~x₁ := v] t₁ }>
  | sumCaseInr (v : Tm) (x₁:String) (t₁ : Tm) (x₂ : String) (t₂ : Tm) (τ₁ : Ty) :
      v.IsValue →
      <{case inr τ₁ v of inl ~x₁ => t₁ | inr ~x₂ => t₂}> ⟶ <{ [~x₂ := v] t₂ }>
  -- lists
  | cons₁ (t₁ t₁' t₂ : Tm) :
      t₁ ⟶ t₁' →
      <{t₁ :: t₂}> ⟶ <{t₁' :: t₂}>
  | cons₂ (v₁ t₂ t₂' : Tm) :
      v₁.IsValue →
      t₂ ⟶ t₂' →
      <{v₁ :: t₂}> ⟶ <{v₁ :: t₂'}>
  | listCase₁ (t₁ t₁' t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
      t₁ ⟶ t₁' →
      <{case t₁ of nil => t₂ | ~x₁ :: ~x₂ => t₃}> ⟶
      <{case t₁' of nil => t₂ | ~x₁ :: ~x₂ => t₃}>
  | listCaseNil (τ₁ : Ty) (t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
      <{case nil τ₁ of nil => t₂ | ~x₁ :: ~x₂ => t₃}> ⟶ t₂
  | listCaseCons (v₁ vl t₂ : Tm) (x₁ x₂ : String) (t₃ : Tm) :
      v₁.IsValue →
      vl.IsValue →
      <{case v₁ :: vl of nil => t₂ | ~x₁ :: ~x₂ => t₃}>
         ⟶  <{ [~x₂ := vl] ([~x₁ := v₁] t₃) }>

  -- Add rules for the following extensions.

  -- pairs
  -- SOLUTION
  | pair₁  (t₁ t₁' t₂ : Tm) :
      t₁ ⟶ t₁' →
      <{ (t₁, t₂) }> ⟶ <{ (t₁' , t₂) }>
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
  -- let
  -- SOLUTION
  | let₁ (x : String) (t₁ t₁' t₂ : Tm) :
      t₁ ⟶ t₁' →
      <{ let ~x = t₁ in t₂}> ⟶ <{ let ~x = t₁' in t₂ }>
  | letValue (x : String) (v₁ t₂ : Tm) :
      v₁.IsValue →
      <{ let ~x = v₁ in t₂ }> ⟶ <{ [~x := v₁] t₂ }>
  -- END SOLUTION
  -- fix
  -- SOLUTION
  | fix₁ (t₁ t₁' : Tm) :
      t₁ ⟶ t₁' →
      <{ fix t₁ }> ⟶ <{ fix t₁' }>
   | fixAbs (x : String) (τ₁ : Ty) (t₁ : Tm) :
      <{ fix (λ ~x : τ₁ . t₁) }> ⟶
      <{ [~x := fix (λ ~x : τ₁ . t₁) ] t₁ }>
  -- END SOLUTION
end

scoped notation:40 t:41 " ⟶ " t':41 => Step t t'
scoped notation:40 t:41 " ⟶* " t':41 => Multi Step t t'

abbrev Context := PartialMap String Ty

inductive HasType : Context → Tm → Ty → Prop where
  -- pure STLC
  | var (Γ : Context) (x : String) (τ₁ : Ty) (h : Γ[x] = some τ₁) :
      <{ Γ ⊢ ~(Tm.var x) ⦂ τ₁ }>
  | abs (Γ : Context) (x : String) (τ₁ τ₂ : Ty) (t₁ : Tm)
      (h : <{ ~x ↦ τ₂ ; Γ ⊢ t₁ ⦂ τ₁ }>) :
      <{ Γ ⊢ λ ~x : τ₂ . t₁ ⦂ τ₂ → τ₁ }>
  | app (Γ : Context) (τ₁ τ₂ : Ty) (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ τ₂ → τ₁ }>) (h₂ : <{ Γ ⊢ t₂ ⦂ τ₂ }>) :
      <{ Γ ⊢ t₁ t₂ ⦂ τ₁ }>
  -- numbers
  | const (Γ : Context) (n : Nat) :
      <{ Γ ⊢ ~(Tm.const n) ⦂ Nat }>
  | succ (Γ : Context) (t₁ : Tm) (h : <{ Γ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ ⊢ succ t₁ ⦂ Nat }>
  | pred (Γ : Context) (t₁ : Tm) (h : <{ Γ ⊢ t₁ ⦂ Nat }>) :
      <{ Γ ⊢ pred t₁ ⦂ Nat }>
  | mult (Γ : Context) (t₁ t₂ : Tm)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Nat }>) (h₂ : <{ Γ ⊢ t₂ ⦂ Nat }>) :
      <{ Γ ⊢ t₁ * t₂ ⦂ Nat }>
  | ite0 (Γ : Context) (t₁ t₂ t₃ : Tm) (τ : Ty)
      (h₁ : <{ Γ ⊢ t₁ ⦂ Nat }>) (h₂ : <{ Γ ⊢ t₂ ⦂ τ }>)
      (h₃ : <{ Γ ⊢ t₃ ⦂ τ }>) :
      <{ Γ ⊢ if0 t₁ then t₂ else t₃ ⦂ τ }>
  -- sums
  | sumInl (Γ : Context) (t₁ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ t₁ ⦂ τ₁ }> →
      <{ ~Γ ⊢ (inl τ₂ t₁) ⦂ τ₁ + τ₂ }>
  | sumInr (Γ : Context) (t₂ : Tm) (τ₁ τ₂ : Ty) :
      <{ ~Γ ⊢ t₂ ⦂ τ₂ }> →
      <{ ~Γ ⊢ (inr τ₁ t₂) ⦂ τ₁ + τ₂ }>
  | sumCase (Γ : Context) (x₁ x₂ : String) (τ₁ τ₂ τ₃: Ty) (t t₁ t₂ : Tm) :
      <{ Γ ⊢ t ⦂ τ₁ + τ₂ }> →
      <{ ~x₁ ↦ τ₁ ; Γ ⊢ t₁ ⦂ τ₃ }> →
      <{ ~x₂ ↦ τ₂ ; Γ ⊢ t₂ ⦂ τ₃ }> →
      <{ ~Γ ⊢ case t of inl ~x₁ => t₁ | inr ~x₂ => t₂ ⦂ τ₃ }>
  -- lists
  | listNil (Γ : Context) (τ₁ : Ty) :
      <{ Γ ⊢ nil τ₁ ⦂ [τ₁] }>
  | listCons (Γ : Context) (t₁ t₂ : Tm) (τ₁ : Ty) :
      <{ Γ ⊢ t₁ ⦂ τ₁ }> →
      <{ Γ ⊢ t₂ ⦂ [τ₁] }> →
      <{ Γ ⊢ t₁ :: t₂ ⦂ [τ₁] }>
  | listCase (Γ : Context) (t₁ t₂ t₃ : Tm) (x₁ x₂ : String) (τ₁ τ₂ : Ty) :
      <{ Γ ⊢ t₁ ⦂ [τ₁] }> →
      <{ Γ ⊢ t₂ ⦂ ~τ₂ }> →
      <{ ~x₁ ↦ τ₁ ; ~x₂ ↦ [τ₁] ; Γ ⊢ t₃ ⦂ τ₂ }> →
      <{ Γ ⊢ case t₁ of nil => t₂ | ~x₁ :: ~x₂ => t₃ ⦂ τ₂ }>
  -- unit
  | unit (Γ : Context) : <{ Γ ⊢ unit ⦂ Unit }>

  -- Add rules for the following extensions.

  -- pairs
  -- SOLUTION
  | pair (Γ : Context) (t₁ t₂ : Tm) (τ₁ τ₂ : Ty) :
      <{ Γ ⊢ t₁ ⦂ τ₁ }> →
      <{ Γ ⊢ t₂ ⦂ τ₂ }> →
      <{ Γ ⊢ (t₁, t₂) ⦂ τ₁ × τ₂ }>
  | fst (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty) :
      <{ Γ ⊢ t ⦂ τ₁ × τ₂ }> →
      <{ Γ ⊢ fst t ⦂ τ₁ }>
  | snd (Γ : Context) (t : Tm) (τ₁ τ₂ : Ty) :
      <{ Γ ⊢ t ⦂ τ₁ × τ₂ }> →
      <{ Γ ⊢ snd t ⦂ τ₂ }>
  -- END SOLUTION
  -- let
  -- SOLUTION
  | letIn (Γ : Context) (x : String) (t₁ t₂ : Tm) (τ₁ τ₂ : Ty) :
      <{ Γ ⊢ t₁ ⦂ τ₁ }> →
      <{ ~x ↦ ~τ₁ ; Γ ⊢ t₂ ⦂ τ₂ }> →
      <{ Γ ⊢ let ~x = t₁ in t₂ ⦂ τ₂ }>
  -- END SOLUTION
  -- fix
  -- SOLUTION
  | fix (Γ : Context) (t₁ : Tm) (τ₁ : Ty) :
      <{ Γ ⊢ t₁ ⦂ τ₁ → τ₁ }> →
      <{ Γ ⊢ fix t₁ ⦂ τ₁ }>
  -- END SOLUTION

open Lean PrettyPrinter in
@[app_unexpander HasType]
def HasType.unexpand : Unexpander := StlcCommon.Delab.unexpandHasType

namespace Sums1

def tm_test :=
  <{ case (inl Nat 5) of
       inl x => x
     | inr y => y }>

theorem typechecks :
    <{ ∅ ⊢ tm_test ⦂ Nat }> := by
  repeat constructor

theorem reduces :
    tm_test ⟶* Tm.const 5 := by
  apply Multi.step
  · apply Step.sumCaseInl
    constructor
  · apply Multi.refl

end Sums1

end StlcExtended
