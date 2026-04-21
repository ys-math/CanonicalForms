import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

import CanonicalForms.Basic
import CanonicalForms.CanonicalForm

namespace CanonicalForms

variable {α β : Type*}

theorem surjective_has_section
    (f : α → β)
    (hf : Function.Surjective f) :
    ∃ g : β → α, IsRetractionSectionPair f g := by
  use fun y => Classical.choose (hf y)
  funext y
  exact Classical.choose_spec (hf y)

theorem canonicalForm_exists
    [s : Setoid α] :
    ∃ C : α → α, IsCanonicalForm (· ≈ ·) C := by
  have hq_surj : Function.Surjective (Quotient.mk s) := Quotient.mk_surjective
  obtain ⟨sec, hsec⟩ := surjective_has_section (Quotient.mk s) hq_surj
  have hC : IsCanonicalForm (· ≈ ·) (sec ∘ Quotient.mk s) := section_to_canonicalForm (sec ∘ Quotient.mk s) sec hsec rfl
  exact ⟨sec ∘ Quotient.mk s, hC⟩


theorem canonicalFormOfCompleteInvariant_exists
    [s : Setoid α]
    (I : α → α)
    (hI : IsCompleteInvariant (· ≈ ·) I) :
    ∃ C : α → α, ∃ sec' : Set.range I → α, C = canonicalFormOfCompleteInvariant  I sec' ∧ IsCanonicalForm (· ≈ ·) C := by
  let I' := corestriction I
  simp only [canonicalFormOfCompleteInvariant]
  change ∃ C sec', C = sec' ∘ I' ∧ IsCanonicalForm (fun x1 x2 => x1 ≈ x2) C
  obtain ⟨C, hC⟩ := @canonicalForm_exists α s
  have hI' : IsCompleteInvariant (· ≈ ·) I' := (corestriction_surjective_completeInvariant s.r I hI).2
  have hI'_surj : Function.Surjective I' := (corestriction_surjective_completeInvariant s.r I hI).1
  obtain ⟨sec', hpair', hCpair'⟩ := (canonicalForm_iff_section_of_completeInvariant I' hI' hI'_surj C).mp hC
  exact ⟨C, sec', hCpair', hC⟩
