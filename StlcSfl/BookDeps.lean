-- Copied and adapted from https://github.com/plclub/sf-in-lean/

def Relation (X : Type) := X → X → Prop

inductive Multi {X : Type} (R : Relation X) : X → X → Prop where
  | refl (x : X) : Multi R x x
  | step (x y z : X) (h₁ : R x y) (h₂ : Multi R y z) : Multi R x z

structure TotalMap (α : Type) (β : Type) where
  inner : α → β

namespace TotalMap

def empty {α β : Type} [Inhabited β] : TotalMap α β where
  inner := fun _ => default

instance {α β : Type} [Inhabited β] : EmptyCollection (TotalMap α β) where
  emptyCollection := TotalMap.empty

theorem empty_def {α β : Type} [Inhabited β] :
    (∅ : TotalMap α β) = { inner := fun _ => default } := by rfl

def get {α β : Type} (m : TotalMap α β) (a : α) := m.inner a

theorem get_def {α β : Type} {m : TotalMap α β} {a : α} : m.get a = m.inner a := by rfl

instance {α β : Type} : GetElem (TotalMap α β) α β (fun _ _ => True) where
  getElem m a _ := m.get a

def update {α β : Type} (m : TotalMap α β) [BEq α] (a : α) (b : β) : TotalMap α β where
  inner := fun a' => bif a == a' then b else m[a']

notation a:55 " →ₜ " b:55 " ; " m:55 => TotalMap.update m a b

/-- This exposes implementation-specific details of `TotalMap`.
  Avoid using this outside the `TotalMap` namespace.
  Prefer `update_apply` if possible. -/
theorem update_def {α β : Type} [BEq α] (m : TotalMap α β) (a : α) (b : β) :
  a →ₜ b ; m = { inner := fun a' => bif a == a' then b else m[a'] } := by rfl

theorem update_apply {α β : Type} [BEq α] (m : TotalMap α β) (a a' : α) (b : β) :
  (a →ₜ b ; m)[a'] = bif a == a' then b else m[a'] := by rfl

@[simp]
theorem getElem_empty {α β : Type} [BEq α] [Inhabited β] (a : α) : (∅ : TotalMap α β)[a] = default := by
  simp only [getElem, empty_def, get_def]

@[simp]
theorem update_eq {α β : Type} [BEq α] [ReflBEq α] (m : TotalMap α β) (a : α) (b : β) : (a →ₜ b ; m)[a] = b := by
  simp [update_def, getElem, get_def]

@[simp]
theorem update_neq {α β : Type} [BEq α] [LawfulBEq α] {m : TotalMap α β} {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) :
    (a₁ →ₜ b ; m)[a₂] = m[a₂] := by
    simp [update_def, getElem, get_def]
    grind

@[ext]
theorem ext {α β : Type} {m₁ m₂ : TotalMap α β} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rw [TotalMap.mk.injEq]
  ext a; specialize h a
  simp [getElem, get_def, get_def] at h
  exact h

@[simp]
theorem update_same {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β) (a : α) : (a →ₜ m[a] ; m) = m := by
    ext a'
    by_cases h : a = a'
    · subst h
      simp
    · simp [update_neq h]

@[simp]
theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α] (m : TotalMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₜ b₂ ; a →ₜ b₁ ; m) = (a →ₜ b₂ ; m) := by
    ext a'
    by_cases h : a = a'
    · subst h
      simp
    · simp [update_neq h]

theorem update_permute {α β : Type} [BEq α] [LawfulBEq α] {m : TotalMap α β} {a₁ a₂ : α} {b₁ b₂ : β} (h : a₁ ≠ a₂) :
    (a₁ →ₜ b₁ ; a₂ →ₜ b₂ ; m) = (a₂ →ₜ b₂ ; a₁ →ₜ b₁ ; m) := by
    ext a
    by_cases h₁ : a₁ = a
    · subst h₁
      rw [update_eq, update_neq h.symm, update_eq]
    · rw [update_neq h₁]
      by_cases h₂ : a₂ = a
      · subst h₂
        rw [update_eq, update_eq]
      · rw [update_neq h₂, update_neq h₂, update_neq h₁]

end TotalMap


structure PartialMap (α : Type) (β : Type) where
  inner : TotalMap α (Option β)

namespace PartialMap

instance {α β : Type} : EmptyCollection (PartialMap α β) where
  emptyCollection := { inner := ∅ }

def toTotal {α β : Type} (m : PartialMap α β) : TotalMap α (Option β) := m.inner

theorem toTotal_def {α β : Type} (m : PartialMap α β) : m.toTotal = m.inner := by rfl

instance {α β : Type} : GetElem (PartialMap α β) α (Option β) (fun _ _ => True) where
  getElem m a _ := m.toTotal[a]

theorem getElem_def {α β : Type} (m : PartialMap α β) (a : α) : m[a] = m.toTotal[a] := rfl

def update {α β : Type} [BEq α] (m : PartialMap α β) (a : α) (b : β) : PartialMap α β :=
  ⟨a →ₜ some b ; m.toTotal⟩

notation a:55 " →ₚ " b:55 " ; " m:55 => PartialMap.update m a b

notation a:55 " →ₚ " b:55 => PartialMap.update ∅ a b

@[simp]
theorem toTotal_empty {α β : Type} : (∅ : PartialMap α β).toTotal = (∅ : TotalMap α (Option β)) := rfl

@[simp]
theorem toTotal_update {α β : Type} [BEq α] (m : PartialMap α β) (a : α) (b : β) :
    (a →ₚ b ; m).toTotal = a →ₜ some b ; m.toTotal := rfl

theorem toTotal_eq_iff {α β : Type} (m₁ m₂ : PartialMap α β) : m₁.toTotal = m₂.toTotal ↔ m₁ = m₂ := by
  rw [mk.injEq]
  rfl

@[ext]
theorem ext {α β : Type} {m₁ m₂ : PartialMap α β} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rw [← toTotal_eq_iff]
  exact TotalMap.ext h

@[simp]
theorem getElem_empty {α β : Type} [BEq α] (a : α) : (∅ : PartialMap α β)[a] = none := by
  rw [getElem_def, toTotal_empty, TotalMap.getElem_empty, Option.default_eq_none]

@[simp]
theorem update_eq {α β : Type} [BEq α] [ReflBEq α] (m : PartialMap α β) (a : α) (b : β) :
    (a →ₚ b ; m)[a] = some b := by
  rw [getElem_def, toTotal_update, TotalMap.update_eq]

@[simp]
theorem update_neq {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a₁ a₂ : α}
    (h : a₁ ≠ a₂) (b : β) : (a₁ →ₚ b ; m)[a₂] = m[a₂] := by
  simp only [getElem_def, toTotal_update]
  rw [TotalMap.update_neq h]

theorem update_shadow {α β : Type} [BEq α] [LawfulBEq α] (m : PartialMap α β) (a : α) (b₁ b₂ : β) :
    (a →ₚ b₂ ; a →ₚ b₁ ; m) = (a →ₚ b₂ ; m) := by
  apply ext
  intro x
  simp only [getElem_def, toTotal_update]
  simp

theorem update_same {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a : α} {b : β}
    (h : m[a] = some b) : (a →ₚ b ; m) = m := by
  apply ext
  intro x
  simp only [getElem, toTotal_update]
  rw [← h]
  simp [getElem_def]

theorem update_permute {α β : Type} [BEq α] [LawfulBEq α] {m : PartialMap α β} {a₁ a₂ : α}
    {b₁ b₂ : β} (h : a₁ ≠ a₂) : (a₁ →ₚ b₁ ; a₂ →ₚ b₂ ; m) = (a₂ →ₚ b₂ ; a₁ →ₚ b₁ ; m) := by
  apply ext
  intro x
  simp only [getElem, toTotal_update]
  rw [TotalMap.update_permute h]

def Subset {α β : Type} (m₁ m₂ : PartialMap α β) : Prop :=
  ∀ {a : α} {b : β}, m₁[a] = some b → m₂[a] = some b

instance {α β : Type} : HasSubset (PartialMap α β) where
  Subset := PartialMap.Subset

theorem subset_def {α β : Type} (m₁ m₂ : PartialMap α β) :
    m₁ ⊆ m₂ ↔ (∀ {a : α} {b : β}, m₁[a] = some b → m₂[a] = some b) := .rfl

theorem update_subset {α β : Type} [BEq α] [LawfulBEq α] (m₁ m₂ : PartialMap α β) (a : α) (b : β)
    (h : m₁ ⊆ m₂) : (a →ₚ b ; m₁) ⊆ (a →ₚ b ; m₂) := by
  rw [subset_def] at h ⊢
  intro a' b' hb
  by_cases ha : a = a'
  · subst ha
    rw [update_eq] at hb ⊢
    exact hb
  · rw [update_neq ha] at hb ⊢
    exact h hb

end PartialMap
