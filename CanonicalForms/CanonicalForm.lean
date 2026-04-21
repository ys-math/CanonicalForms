import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

import CanonicalForms.Basic

namespace CanonicalForms

variable {α β γ : Type*}

structure IsCanonicalForm (r : α → α → Prop) (C : α → α) : Prop where
  inv    : IsInvariant r C
  equiv  : ∀x : α, r x (C x)

def skeleton (C : α → α) : Set α := Set.range C

theorem canonicalForm_idempotent (r : α → α → Prop) (C : α → α) (hC : IsCanonicalForm r C) : C ∘ C = C := by
  funext x
  exact (hC.inv x (C x) (hC.equiv x)).symm

theorem canonicalForm_to_section [s : Setoid α]
    (C : α → α)
    (hC : IsCanonicalForm (· ≈ ·) C) :
    ∃ sec : Quotient s → α, IsRetractionSectionPair (Quotient.mk s) sec ∧ C = sec ∘ Quotient.mk s := by
  use Quotient.lift C (fun x y hxy => hC.inv x y hxy)
  refine ⟨?_section, ?_factoring⟩
  · funext q
    induction q using Quotient.ind with
    | _ x =>
      simp [Function.comp]
      rw [← Quotient.sound]
      exact hC.equiv x
  · funext x
    simp [Function.comp]

theorem section_to_canonicalForm [s : Setoid α]
    (C : α → α)
    (sec : Quotient s → α)
    (hpair : IsRetractionSectionPair (Quotient.mk s) sec)
    (hfact : C = sec ∘ Quotient.mk s) :
    IsCanonicalForm (· ≈ ·) C := by
  refine ⟨?_inv, ?_equiv⟩
  · intro x y hxy
    simp [hfact]
    exact congr_arg sec (Quotient.sound hxy)
  · intro x
    simp only [IsRetractionSectionPair] at hpair
    rw [hfact]
    exact Quotient.exact (congr_fun hpair ⟦x⟧).symm

theorem canonicalForm_iff_section [s : Setoid α]
    (C : α → α) :
    IsCanonicalForm (· ≈ ·) C ↔ ∃ sec : Quotient s → α, IsRetractionSectionPair (Quotient.mk s) sec ∧ C = sec ∘ Quotient.mk s := by
  constructor
  · exact canonicalForm_to_section C
  · rintro ⟨sec, hpair, hfact⟩
    exact section_to_canonicalForm C sec hpair hfact

theorem canonicalForm_iff_section_of_completeInvariant [s : Setoid α]
  (I : α → β)
  (hInv : IsCompleteInvariant (· ≈ ·) I)
  (hSurj : Function.Surjective I)
  (C : α → α) :
  IsCanonicalForm (· ≈ ·) C ↔ ∃ sec' : β → α, IsRetractionSectionPair I sec' ∧ C = sec' ∘ I := by
  rw [canonicalForm_iff_section]
  have hInv' : IsInvariant (· ≈ ·) I := hInv.toIsInvariant
  let Ibar : Quotient s → β :=
    Quotient.lift I (fun x y hxy => hInv' x y hxy)
  have hIbar_inj : Function.Injective Ibar := by
    intro q₁ q₂ heq
    induction q₁ using Quotient.ind with
    | _ x =>
      induction q₂ using Quotient.ind with
      | _ y =>
      simp [Ibar] at heq
      exact Quotient.sound ((hInv x y).mpr heq)
  have hIbar_surj : Function.Surjective Ibar := by
    intro b
    obtain ⟨x, hx⟩ := hSurj b
    exact ⟨Quotient.mk s x, hx⟩
  have hIbar_bij : Function.Bijective Ibar := ⟨hIbar_inj, hIbar_surj⟩
  let hIbar_inv : β → Quotient s := Function.surjInv hIbar_surj
  have hIpair : I = Ibar ∘ Quotient.mk s := by
    funext x
    exact Eq.symm Function.comp_apply
  constructor
  · intro hCan
    obtain ⟨sec, hpair, hfact⟩ := hCan
    let sec' : β → α := sec ∘ hIbar_inv
    have hpair' : IsRetractionSectionPair I sec' := by
      funext x
      rw [hIpair]
      simp only [sec']
      change (Ibar ∘ (Quotient.mk s ∘ sec) ∘ hIbar_inv) x = id x
      simp only [IsRetractionSectionPair] at hpair
      rw [hpair]
      rw [Function.id_comp]
      simp only [hIbar_inv]
      exact Function.surjInv_eq hIbar_surj x
    have hCpair' : C = sec' ∘ I := by
      funext x
      simp only [sec']
      rw [hfact]
      simp
      congr
      simp only [hIpair]
      change ⟦x⟧ = (hIbar_inv ∘ Ibar) ⟦x⟧
      simp only [hIbar_inv]
      exact (Function.leftInverse_surjInv hIbar_bij ⟦x⟧).symm
    exact ⟨sec', hpair', hCpair'⟩
  · intro hCan'
    obtain ⟨sec', hpair', hfact'⟩ := hCan'
    let sec : Quotient s → α := sec' ∘ Ibar
    have hpair : IsRetractionSectionPair (Quotient.mk s) sec := by
      funext y
      simp only [sec]
      induction y using Quotient.ind with
      | _ x =>
        change (Quotient.mk s ∘ sec' ∘ Ibar ∘ Quotient.mk s) x = ⟦x⟧
        rw [← hIpair, ← hfact']
        simp
        apply Quotient.sound
        apply (hInv (C x) x).mpr
        simp only [hfact', Function.comp]
        simp only [IsRetractionSectionPair] at hpair'
        exact congr_fun hpair' (I x)
    have hCpair : C = sec ∘ Quotient.mk s := by
      simp only [sec]
      rw [Function.comp_assoc, ← hIpair]
      exact hfact'
    exact ⟨sec, hpair, hCpair⟩
