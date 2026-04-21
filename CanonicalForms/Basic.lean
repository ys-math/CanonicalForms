import Mathlib.Tactic

namespace CanonicalForms

variable {α β γ : Type*}

def IsInvariant
    (r : α → α → Prop)
    (f : α → β) :
    Prop :=
  ∀x y : α, r x y → f x = f y

def IsCompleteInvariant
    (r : α → α → Prop)
    (f : α → β) :
    Prop :=
  ∀x y : α, r x y ↔ f x = f y

theorem IsCompleteInvariant.toIsInvariant
    (r : α → α → Prop)
    (f : α → β)
    (hf : IsCompleteInvariant r f) :
    IsInvariant r f := by
  intro x y hxy
  exact (hf x y).mp hxy

theorem quotientMap_isCompleteInvariant
    [s : Setoid α] :
    IsCompleteInvariant (· ≈ ·) (Quotient.mk s) := by
  intro x y
  constructor
  · exact Quotient.sound
  · exact Quotient.exact

def IsRetractionSectionPair
    (r : α → β)
    (s : β → α) :
    Prop :=
  r ∘ s = id

theorem IsRetractionSectionPair.pointwise
    (r : α → β)
    (s : β → α)
    (h : IsRetractionSectionPair r s) :
    ∀ y : β, r (s y) = y := by
  intro y
  exact congr_fun h y

theorem IsRetractionSectionPair.section_injective
    (r : α → β)
    (s : β → α)
    (h : IsRetractionSectionPair r s) :
    Function.Injective s := by
  intro y₁ y₂ heq
  have := congr_arg r heq
  simp [h.pointwise r s] at this
  exact this

theorem corestriction_surjective_completeInvariant
    (r : α → α → Prop)
    (I : α → β)
    (hI : IsCompleteInvariant r I) :
    let I' : α → Set.range I := fun x => ⟨I x, Set.mem_range_self x⟩
    Function.Surjective I' ∧ IsCompleteInvariant r I' := by
  simp only
  constructor
  · intro ⟨y, x, hx⟩
    exact ⟨x, by simp [hx]⟩
  · intro x y
    simp
    exact hI x y

def corestriction (I : α → β) : α → Set.range I :=
  fun x => ⟨I x, Set.mem_range_self x⟩

def canonicalFormOfCompleteInvariant
    (I : α → β)
    (s' : Set.range I → α) :
    α → α :=
  s' ∘ corestriction I
