import CanonicalForms.CanonicalForm

namespace CanonicalForms

variable {α β : Type*}

-- theory_en.tex / theory_ja.tex: Lemma 2 (AC) (a surjection has a section)
theorem surjective_has_section
    (f : α → β)
    (hf : Function.Surjective f) :
    ∃ g : β → α, IsRetractionSectionPair f g := by
  use fun y => Classical.choose (hf y)
  funext y
  exact Classical.choose_spec (hf y)

-- Helper lemma (no numbered TeX counterpart; follows from Lemma 1 and Lemma 2 (AC)):
-- a canonical form exists, via a section of the quotient map.
theorem canonicalForm_exists
    [s : Setoid α] :
    ∃ C : α → α, IsCanonicalForm (· ≈ ·) C := by
  have hq_surj : Function.Surjective (Quotient.mk s) := Quotient.mk_surjective
  obtain ⟨sec, hsec⟩ := surjective_has_section (Quotient.mk s) hq_surj
  have hC : IsCanonicalForm (· ≈ ·) (sec ∘ Quotient.mk s) := section_to_canonicalForm (sec ∘ Quotient.mk s) sec hsec rfl
  exact ⟨sec ∘ Quotient.mk s, hC⟩


-- theory_en.tex / theory_ja.tex: Proposition 5 (AC) (a section s' of I' exists, and hence a canonical form determined by I and s')
theorem canonicalFormOfCompleteInvariant_exists
    [s : Setoid α]
    (I : α → β)
    (hI : IsCompleteInvariant (· ≈ ·) I) :
    ∃ s' : Set.range I → α,
      IsRetractionSectionPair (corestriction I) s' ∧
      IsCanonicalForm (· ≈ ·) (canonicalFormOfCompleteInvariant I s') := by
  obtain ⟨hsurj, -⟩ := corestriction_surjective_completeInvariant s.r I hI
  obtain ⟨s', hs'⟩ := surjective_has_section (corestriction I) hsurj
  exact ⟨s', hs', canonicalFormOfCompleteInvariant_isCanonicalForm I hI s' hs'⟩
