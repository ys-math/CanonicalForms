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
  simp only [h.pointwise ret sec] at this
  exact this

-- theory_en.tex / theory_ja.tex: Proposition 3 (the unique map I' : X → I(X) with I = i ∘ I')
def corestriction (I : α → β) : α → Set.range I :=
  fun x => ⟨I x, Set.mem_range_self x⟩

-- theory_en.tex / theory_ja.tex: Proposition 3 (existence of I': the corestriction satisfies I = i ∘ I')
theorem val_comp_corestriction (I : α → β) :
    Subtype.val ∘ corestriction I = I :=
  rfl

-- theory_en.tex / theory_ja.tex: Proposition 3 (uniqueness of I': every J with I = i ∘ J is the corestriction)
theorem corestriction_unique
    (I : α → β)
    (J : α → Set.range I)
    (hJ : Subtype.val ∘ J = I) :
    J = corestriction I := by
  funext x
  apply Subtype.ext
  exact congr_fun hJ x

-- theory_en.tex / theory_ja.tex: Proposition 3 (existence and uniqueness of I' : X → I(X) with I = i ∘ I')
theorem corestriction_existsUnique (I : α → β) :
    ∃! J : α → Set.range I, Subtype.val ∘ J = I :=
  ⟨corestriction I, val_comp_corestriction I, fun J hJ => corestriction_unique I J hJ⟩

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
    simp only [corestriction, Subtype.mk.injEq]
    exact hI x y

-- theory_en.tex / theory_ja.tex: Definition 4 (canonical form s' ∘ I' of ∼ determined by I and s')
def canonicalFormOfCompleteInvariant
    (I : α → β)
    (s' : Set.range I → α) :
    α → α :=
  s' ∘ corestriction I

-- Mathlib bridge (no numbered TeX counterpart): relates IsRetractionSectionPair to Mathlib's
-- Function.RightInverse; sec is a section of ret iff sec is a right inverse of ret.
theorem isRetractionSectionPair_iff_rightInverse
    (ret : α → β)
    (sec : β → α) :
    IsRetractionSectionPair ret sec ↔ Function.RightInverse sec ret :=
  Function.rightInverse_iff_comp.symm

-- Mathlib bridge (no numbered TeX counterpart): relates IsCompleteInvariant to Mathlib's
-- Setoid.ker; f is a complete invariant of the setoid s iff the kernel of f is s.
theorem isCompleteInvariant_iff_ker_eq
    [s : Setoid α]
    (f : α → β) :
    IsCompleteInvariant (· ≈ ·) f ↔ Setoid.ker f = s := by
  constructor
  · intro hf
    ext x y
    exact (hf x y).symm
  · intro hker x y
    subst hker
    exact Iff.rfl

-- Mathlib bridge (no numbered TeX counterpart): relates corestriction to Mathlib's
-- Set.rangeFactorization; the corestriction of I is the range factorization of I.
theorem corestriction_eq_rangeFactorization (I : α → β) :
    corestriction I = Set.rangeFactorization I :=
  rfl
