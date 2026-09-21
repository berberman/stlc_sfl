import Lean
import StlcSfl.BookDeps

namespace StlcCommon

declare_syntax_cat stlcTy

syntax:max "~" term:max : stlcTy
syntax:max "(" stlcTy ")" : stlcTy
syntax:max ident : stlcTy
syntax:50 stlcTy:51 " → " stlcTy:50 : stlcTy
syntax:50 stlcTy:51 " -> " stlcTy:50 : stlcTy

syntax:max (name := tyBracket) "<{ " stlcTy " }>" : term

declare_syntax_cat stlcVar

syntax:max ident : stlcVar
syntax:max "~" term:max : stlcVar

declare_syntax_cat stlcTm

syntax:max "~" term:max : stlcTm
syntax:max "(" stlcTm ")" : stlcTm
syntax:max ident : stlcTm
syntax:75 stlcTm:75 ppSpace stlcTm:76 : stlcTm
syntax:50 "λ " stlcVar " : " stlcTy " . " stlcTm:50 : stlcTm
syntax:max "[" stlcVar " := " stlcTm "] " stlcTm:max : stlcTm

syntax:max (name := tmBracket) "<{ " stlcTm " }>" : term

declare_syntax_cat stlcCtx

syntax:max "∅" : stlcCtx
syntax:max "~" term:max : stlcCtx
syntax:max ident : stlcCtx
syntax:max stlcVar " ↦ " stlcTy " ; " stlcCtx : stlcCtx

syntax:max (name := ctxBracket) "<{ " stlcCtx " }>" : term

syntax:max (name := judgeBracket)
  "<{ " stlcCtx " ⊢ " stlcTm " ⦂ " stlcTy " }>" : term

namespace Elab

open Lean Elab Term Meta

def withSourceInfoOf {kind : Name} (ref : Syntax) (stx : TSyntax kind)
    (canonical := true) : TSyntax kind :=
  let info := SourceInfo.fromRef ref (canonical := canonical)
  ⟨stx.raw.setInfo info⟩

def mkObjectIdentFrom (ref : Syntax) (name : String) : Ident :=
  mkIdentFrom ref (Name.mkSimple name)

structure Language where
  tyType : Name
  tmType : Name

  arrowCtor : Name
  varCtor   : Name
  appCtor   : Name
  absCtor   : Name

  subst : Name
  hasType  : Name

def Language.mkArrow (lang : Language) (A B : Expr) : Expr :=
  mkApp2 (mkConst lang.arrowCtor) A B

def Language.mkVar (lang : Language) (x : String) : Expr :=
  mkApp (mkConst lang.varCtor) (mkStrLit x)

def Language.mkApp (lang : Language) (f a : Expr) : Expr :=
  mkApp2 (mkConst lang.appCtor) f a

def Language.mkAbs (lang : Language) (x T body : Expr) : Expr :=
  mkApp3 (mkConst lang.absCtor) x T body

/-! See the note on `Language.mkHasType`. -/
def Language.mkSubst (lang : Language) (x s t : Expr) : TermElabM Expr := do
  let some subst ← resolveId? (mkIdent lang.subst)
    | throwError "unknown declaration `{lang.subst}`"
  return mkApp3 subst x s t

-- Fixed to `PartialMap String Ty`
def Language.ctxType (lang : Language) : Expr :=
  mkApp2 (mkConst ``PartialMap) (mkConst ``String) (mkConst lang.tyType)

def Language.mkEmptyCtx (lang : Language) : TermElabM Expr := do
  let stx ← `(∅)
  elabTermEnsuringType stx lang.ctxType

def Language.mkExtendCtx (_lang : Language) (Γ x T : Expr) : TermElabM Expr :=
  mkAppM ``PartialMap.update #[Γ, x, T]

/-!
Trick: resolve the forward-referenced `hasType` here
so that `HasType` notation is aviable when defining `HasType`.
This relies on Lean's `inductive` elabrator implementation detail:
an auxiliary fvar of the inductive type being defined is created
before the consturctors are elaborated to represent this inductive type,
because the constructors need to refer the inductive type.
So once we resolve `HasType`, that auxiliary fvar is correctly used.
I (berberman) think this is better than macro-based notation with `set_option hygiene false`.
-/
def Language.mkHasType (lang : Language) (Γ t T : Expr) : TermElabM Expr := do
  let some hasType ← resolveId? (mkIdent lang.hasType)
    | throwError "unknown declaration `{lang.hasType}`"
  return mkApp3 hasType Γ t T

structure Binding where
  name : String
  fvar : Expr
  lctx : LocalContext

abbrev Scope := List Binding
abbrev FVars := List Binding

def identString (id : Ident) : String :=
  id.getId.eraseMacroScopes.toString

def lookupBinding
    (Γ : List Binding)
    (name : String) : Option Binding :=
  Γ.find? fun b =>
    b.name == name


def addBindingInfo
    (id : Ident)
    (binding : Binding)
    (isBinder := false) : TermElabM Unit :=
  addTermInfo' id binding.fvar (lctx? := some binding.lctx) (isBinder := isBinder)


def mkSyntheticBinding
    (lang : Language)
    (id : Ident) : TermElabM Binding :=
  withLocalDeclD id.getId (mkConst lang.tmType) fun fvar => do
    let lctx ← getLCtx
    return {
      name := identString id
      fvar
      lctx
    }

def mkBinder
    (lang : Language)
    (id : Ident) : TermElabM Binding := do
  let binding ← mkSyntheticBinding lang id
  addBindingInfo id binding (isBinder := true)
  return binding

/-!
A bare Lean value of the target `Tm` type may be implicitly antiquoted.
A `String` is never implicitly interpreted as an object-language variable name.
-/
def resolveVar? (expectedType : Expr)
    (id : Ident) : TermElabM (Option Expr) := do
  let some e ← resolveId? id (withInfo := false)
    | return none
  -- The following conservative approach would
  -- fail if the type is an mvar,
  -- e.g. `¬ ∃ S T, <{ ∅ ⊢ λ x : S . x x ⦂ T }>`
  --
  -- let type ← whnf (← inferType e)
  -- tryPostponeIfMVar type
  -- if type.isConstOf targetType then
  --   addTermInfo' id e
  --   return some e
  --
  -- In this example, we know `S` and `T` have to be `Ty` in order to make sense!
  -- So Let's solve them instead.
  let type ← inferType e
  if ← isDefEq type expectedType then
    addTermInfo' id e
    return some e
  else
    return none

def resolveTmVar?
    (lang : Language)
    (id : Ident) : TermElabM (Option Expr) :=
  resolveVar? (mkConst lang.tmType) id

def resolveTyVar?
    (lang : Language)
    (id : Ident) : TermElabM (Option Expr) :=
  resolveVar? (mkConst lang.tyType) id


def resolveCtxVar?
    (lang : Language)
    (id : Ident) : TermElabM (Option Expr) :=
  resolveVar? lang.ctxType id

/-!
A bare `x` denotes the literal object-language name `"x"`.
Only `~x` splices a Lean `String`.
This policy is shared by lambda binders and substitution targets.
-/
def elabStlcVarName (x : TSyntax `stlcVar) : TermElabM Expr :=
  match x with
  | `(stlcVar| $id:ident) =>
      return mkStrLit (identString id)
  | `(stlcVar| ~$e:term) =>
      elabTermEnsuringType e (mkConst ``String)
  | _ => throwUnsupportedSyntax

def elabStlcBinder
    (lang : Language)
    (Γ : Scope)
    (x : TSyntax `stlcVar) :
    TermElabM (Expr × Scope) := do
  match x with
  -- Static binder: create new Lean fvar in lexical STLC scope
  | `(stlcVar| $id:ident) => do
      let binding ← mkBinder lang id
      return (mkStrLit binding.name, binding :: Γ)
  -- Dynamic binder name: don't create the fvar as the String value is only known at runtime
  | `(stlcVar| ~$name:term) => do
      let name ← elabTermEnsuringType name (mkConst ``String)
      return (name, Γ)
  | _ => throwUnsupportedSyntax

/-!
Two different continuations:
* `recur` elaborates a child using the complete language.
* `k` continues with the next handler when this handler does not recognize
  the current syntax node.
-/

abbrev TyElab := TSyntax `stlcTy → TermElabM Expr

abbrev TyElabHandler := (recur : TyElab) → (k : TyElab) → TyElab

abbrev TmElab :=
  Scope →
  FVars →
  TSyntax `stlcTm →
  TermElabM (Expr × FVars)

abbrev TmElabHandler := (recur : TmElab) → (k : TmElab) → TmElab

def TyElabHandler.orElse
    (first second : TyElabHandler) :
    TyElabHandler :=
  fun recur k => first recur (second recur k)

def TmElabHandler.orElse
    (first second : TmElabHandler) :
    TmElabHandler :=
  fun recur k => first recur (second recur k)

def unsupportedTy : TyElab :=
  fun _ => throwUnsupportedSyntax

def unsupportedTm : TmElab :=
  fun _ _ _ => throwUnsupportedSyntax

/-- Handles:
* `~` antiquotation
* parentheses
* arrows
* implicit Lean `Ty` antiquotation
-/
def commonTyHandler (lang : Language) : TyElabHandler :=
  fun recur k T => do
    match T with
    | `(stlcTy| ~$e:term) =>
        elabTermEnsuringType e (mkConst lang.tyType)
    | `(stlcTy| ($T:stlcTy)) =>
        recur T
    | `(stlcTy| $A:stlcTy → $B:stlcTy) => do
        let A ← recur A
        let B ← recur B
        return lang.mkArrow A B
    | `(stlcTy| $A:stlcTy -> $B:stlcTy) => do
        let A ← recur A
        let B ← recur B
        return lang.mkArrow A B
    | `(stlcTy| $id:ident) =>
        if let some e ← resolveTyVar? lang id then
          return e
        else
          k T
    | _ => k T

/--
Handles:
* `~` antiquotation
* variables
* application
* parentheses
* lambda
* substitution
-/
def commonTmHandler
    (lang : Language)
    (elabTy : TyElab) :
    TmElabHandler :=
  fun recur k Γ free t => do
    match t with
    -- Explicit ~ antiquotation
    | `(stlcTm| ~$e:term) =>
        return ( ← elabTermEnsuringType e (mkConst lang.tmType), free)

    -- Variable occurrence
    | `(stlcTm| $id:ident) => do
        let name := identString id
        -- 1. Lexically bound object variable.
        if let some binding := lookupBinding Γ name then
          addBindingInfo id binding
          return (lang.mkVar name, free)
        -- 2. Implicit Lean `Tm` antiquotation.
        if let some e ← resolveTmVar? lang id then
          return (e, free)
        -- 3. Existing free object variable.
        if let some binding := lookupBinding free name then
          addBindingInfo id binding
          return (lang.mkVar name, free)
        -- 4. First occurrence of this free object variable.
        let binding ← mkSyntheticBinding lang id
        addBindingInfo id binding
        return (lang.mkVar name, binding :: free )

    -- Substitution
    | `(stlcTm| [$x:stlcVar := $s:stlcTm] $t:stlcTm) => do
        /-
        Name position:
          `[x := s] t` means `"x"`
          `[~x := s] t` `splices x : String`
          NO automatic `String` antiquotation.
        -/
        let x ← elabStlcVarName x
        let (s, free) ← recur Γ free s
        let (t, free) ← recur Γ free t
        return (← lang.mkSubst x s t, free)

    -- Application
    | `(stlcTm| $f:stlcTm $a:stlcTm) => do
        let (f, free) ← recur Γ free f
        let (a, free) ← recur Γ free a
        return (lang.mkApp f a, free)

    -- Parentheses
    | `(stlcTm| ($t:stlcTm)) =>
        recur Γ free t

    -- Lambda
    | `(stlcTm| λ $x:stlcVar : $T:stlcTy . $body:stlcTm) => do
        let T ← elabTy T
        let (x, Γ) ← elabStlcBinder lang Γ x
        let (body, free) ← recur Γ free body
        return (lang.mkAbs x T body, free)

    | _ => k Γ free t


abbrev CtxElab := TSyntax `stlcCtx → TermElabM (Expr × Scope)

partial def elabCtxCommon
    (lang : Language)
    (elabTy : TyElab)
    (Γ : TSyntax `stlcCtx) :
    TermElabM (Expr × Scope) := do
  match Γ with
  -- Empty object context.
  | `(stlcCtx| ∅) => do
      return (← lang.mkEmptyCtx, [])
  | `(stlcCtx| $id:ident) => do
      if let some Γ ← resolveCtxVar? lang id then
        return (Γ, [])
      else
        throwErrorAt id "expected a Lean identifier of type `{lang.ctxType}`"
  -- Dynamic Lean context
  | `(stlcCtx| ~$Γ:term) => do
      let Γ ← elabTermEnsuringType Γ lang.ctxType
      return (Γ, [])
  -- Static context extension
  | `(stlcCtx| $x:stlcVar ↦ $T:stlcTy ; $Γ:stlcCtx) => do
      let (Γ, scope) ← elabCtxCommon lang elabTy Γ
      let T ← elabTy T
      match x with
      -- Static name: create new Lean fvar
      | `(stlcVar| $id:ident) => do
          let binding ← mkBinder lang id
          return (
            ← lang.mkExtendCtx Γ (mkStrLit binding.name) T,
            binding :: scope
          )
      -- Dynamic name
      | `(stlcVar| ~$name:term) => do
          let name ← elabTermEnsuringType name (mkConst ``String)
          return (← lang.mkExtendCtx Γ name T, scope)
      | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax
end Elab

namespace Delab

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer Elab

@[category_parenthesizer stlcTy]
def stlcTy.parenthesizer : CategoryParenthesizer
  | prec => do
      maybeParenthesize `stlcTy true wrapParens prec <|
        parenthesizeCategoryCore `stlcTy prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTy| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

@[category_parenthesizer stlcTm]
def stlcTm.parenthesizer : CategoryParenthesizer
  | prec => do
      maybeParenthesize `stlcTm true wrapParens prec <|
        parenthesizeCategoryCore `stlcTm prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(stlcTm| ($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

def getTy (stx : Term) : TSyntax `stlcTy :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(<{ $T:stlcTy }>) => return T
    | `((<{ $T:stlcTy }>)) => return T
    | `($T:ident) => `(stlcTy| $T:ident)
    | _ => `(stlcTy| ~$stx)


def getTm (stx : Term) : TSyntax `stlcTm :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `(<{ $t:stlcTm }>) => return t
    | `((<{ $t:stlcTm }>)) => return t
    | `($t:ident) => `(stlcTm| $t:ident)
    | _ => `(stlcTm| ~$stx)

def isPlainName (s : String) : Bool :=
  !s.isEmpty &&
  s != "_" &&
  !s.front.isDigit &&
  s.all fun c => c.isAlphanum || c == '_'

def getVar (stx : Term) : TSyntax `stlcVar :=
  withSourceInfoOf (canonical := false) stx <| Unhygienic.run do
    match stx with
    | `($s:str) =>
        if isPlainName s.getString then
          `(stlcVar| $(mkIdentFrom stx (Name.mkSimple s.getString)):ident)
        else
          `(stlcVar| ~$s)
    | _ => `(stlcVar| ~$stx)

/-- Each language provides its `reserved` identifiers (to not be printed as ordinary variables) -/
def unexpandVar (reserved : String → Bool) (varCtor : Name) : Unexpander
  | stx@`($_ $s:str) =>
      if isPlainName s.getString && !reserved s.getString then
        do
          let t := mkObjectIdentFrom stx s.getString
          let t ← `(stlcTm|$t:ident)
          `(<{ $t:stlcTm }>)
      else
        pure <| Unhygienic.run do
          let var : Term := mkIdentFrom stx varCtor
          return (← `($var $s)).raw
  | _ => throw ()

def delabVar (varCtor : Name) : Delab :=
  whenPPOption getPPNotation do
    let e ← getExpr
    guard <| e.isAppOfArity varCtor 1
    match e.appArg! with
    | .lit (.strVal _) => failure
    | _ => do
        let var : Term := mkIdent varCtor
        `($var $(← withAppArg delab))

def unexpandArrow : Unexpander
  | `($_ $A $B) => `(<{ $(getTy A) → $(getTy B) }>)
  | _ => throw ()

def unexpandApp : Unexpander
  | `($_ $f $a) => `(<{ $(getTm f) $(getTm a) }>)
  | _ => throw ()

def unexpandAbs : Unexpander
  | `($_ $x $T $t) => `(<{ λ $(getVar x) : $(getTy T) . $(getTm t) }>)
  | _ => throw ()

def unexpandSubst : Unexpander
  | `($_ $x $s $t) => `(<{ [$(getVar x) := $(getTm s)] $(getTm t) }>)
  | _ => throw ()

partial def unexpandCtx :
    Term → UnexpandM (TSyntax `stlcCtx)
  | `(∅) => `(stlcCtx| ∅)
  | `($x:str →ₚ $T) => do unexpandCtx (← `($x →ₚ $T ; ∅))
  | `($x:str →ₚ $T ; $Γ) => do
      let Γ' ← unexpandCtx Γ
      let x' := getVar x
      let T' := getTy T
      `(stlcCtx| $x':stlcVar ↦ $T':stlcTy ; $Γ':stlcCtx)
  | `($Γ:ident) => `(stlcCtx| $Γ:ident)
  | Γ => `(stlcCtx| ~$Γ)

def unexpandHasType : Unexpander
  | `($_ $Γ $t $T) => do
      let Γ' ← unexpandCtx Γ
      let t' := getTm t
      let T' := getTy T
      `(<{ $Γ':stlcCtx ⊢ $t':stlcTm ⦂ $T':stlcTy }>)
  | _ => throw ()

end Delab

end StlcCommon
