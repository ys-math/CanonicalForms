import Mathlib.Tactic

namespace CanonicalForms

variable {α β γ : Type*}

-- theory_en.tex / theory_ja.tex: Definition 1 (invariant)
def IsInvariant
    (r : α → α → Prop)
    (f : α → β) :
    Prop :=
  ∀x y : α, r x y → f x = f y

-- theory_en.tex / theory_ja.tex: Definition 1 (complete invariant)
def IsCompleteInvariant
    (r : α → α → Prop)
    (f : α → β) :
    Prop :=
  ∀x y : α, r x y ↔ f x = f y

-- Helper lemma (no numbered TeX counterpart): a complete invariant is an invariant.
theorem IsCompleteInvariant.toIsInvariant
    (r : α → α → Prop)
    (f : α → β)
    (hf : IsCompleteInvariant r f) :
    IsInvariant r f := by
  intro x y hxy
  exact (hf x y).mp hxy

-- theory_en.tex / theory_ja.tex: Example 1 (the quotient map is a complete invariant)
theorem quotientMap_isCompleteInvariant
    [s : Setoid α] :
    IsCompleteInvariant (· ≈ ·) (Quotient.mk s) := by
  intro x y
  constructor
  · exact Quotient.sound
  · exact Quotient.exact

-- theory_en.tex / theory_ja.tex: Definition 3 (retraction–section pair)
def IsRetractionSectionPair
    (ret : α → β)
    (sec : β → α) :
    Prop :=
  ret ∘ sec = id

-- Helper lemma (no numbered TeX counterpart): pointwise form of a retraction–section pair.
theorem IsRetractionSectionPair.pointwise
    (ret : α → β)
    (sec : β → α)
    (h : IsRetractionSectionPair ret sec) :
    ∀ y : β, ret (sec y) = y := by
  intro y
  exact congr_fun h y

-- Helper lemma (no numbered TeX counterpart): the section of a retraction–section pair is injective.
theorem IsRetractionSectionPair.section_injective
    (ret : α → β)
    (sec : β → α)
    (h : IsRetractionSectionPair ret sec) :
    Function.Injective sec := by
  intro y₁ y₂ heq
  have := congr_arg ret heq
  simp [h.pointwise ret sec] at this
  exact this

-- theory_en.tex / theory_ja.tex: Proposition 3 (the unique map I' : X → I(X) with I = i ∘ I')
def corestriction (I : α → β) : α → Set.range I :=
  fun x => ⟨I x, Set.mem_range_self x⟩

-- theory_en.tex / theory_ja.tex: Proposition 3 (the corestriction I' is surjective and a complete invariant)
theorem corestriction_surjective_completeInvariant
    (r : α → α → Prop)
    (I : α → β)
    (hI : IsCompleteInvariant r I) :
    Function.Surjective (corestriction I) ∧ IsCompleteInvariant r (corestriction I) := by
  constructor
  · intro ⟨y, x, hx⟩
    exact ⟨x, by simp [corestriction, hx]⟩
  · intro x y
    simp [corestriction]
    exact hI x y

-- theory_en.tex / theory_ja.tex: Definition 4 (canonical form s' ∘ I' determined by the complete invariant I)
def canonicalFormOfCompleteInvariant
    (I : α → β)
    (s' : Set.range I → α) :
    α → α :=
  s' ∘ corestriction I
