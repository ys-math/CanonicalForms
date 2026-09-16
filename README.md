# CanonicalForms

A Lean 4 formalization of invariants and canonical forms for equivalence relations.

[![Build Status](https://github.com/ys-math/CanonicalForms/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/ys-math/CanonicalForms/actions/workflows/lean_action_ci.yml)

---

## Mathematical Content

Given an equivalence relation `∼` on a type `α`, this project formalizes the following hierarchy of concepts.

A function `f : α → β` is an **invariant** of `∼` if equivalent elements have equal images. It is a **complete invariant** if the converse also holds. A function `C : α → α` that is an invariant of `∼` and satisfies `x ∼ C x` for all `x` is called a **canonical form** of `∼`. The image `C(α)` is called the **skeleton** or the **complete system of representatives** of `∼`.

The central results include a structural characterization of canonical forms via retraction-section pairs and a proof, assuming the axiom of choice, that every complete invariant determines a canonical form.

For the complete natural language proofs, see the following documents.

- English: [`docs/theory_en.pdf`](docs/theory_en.pdf)
- Japanese: [`docs/theory_ja.pdf`](docs/theory_ja.pdf)

---

## Repository Structure

```
CanonicalForms/
├── CanonicalForms/
│   ├── Basic.lean                 # IsInvariant, IsCompleteInvariant
│   ├── CanonicalForm.lean         # IsCanonicalForm, skeleton
│   └── Existence.lean             # Existence theorem (AC)
└── docs/
    ├── theory_en.pdf              # Natural language proof (English)
    ├── theory_en.tex
    ├── theory_ja.pdf              # Natural language proof (Japanese)
    └── theory_ja.tex
```

---

## References

- [Mathlib4: Setoid](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Setoid/Basic.html)
- [Mathlib4: Quotient](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quotient)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [The Lean Language Reference/Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/#quotients)


---

## Use of AI

AI models are used in this project for planning, documentation, annotation, and build and CI configuration (including `scripts/CheckAxioms.lean`). The mathematical statements and their Lean proofs are written and verified by the author, except for the following changes, which the author requested and Claude Code (Claude Opus 5) made.

- `canonicalFormOfCompleteInvariant_exists` (Proposition 4): the statement was replaced by one given by the author, which takes a map `I : α → β` and states that `s'` is a section of `corestriction I`. The AI adapted the proof to the new statement. The AI also added the hypothesis that `I` is a complete invariant to Proposition 4 in `docs/theory_en.tex` and `docs/theory_ja.tex`, and rebuilt both PDFs.
- `corestriction_surjective_completeInvariant` (Proposition 3): as specified by the author, the statement now uses `corestriction` instead of a `let`. The AI moved the definition of `corestriction` above the theorem and adapted the proof.
- `IsRetractionSectionPair`, `IsRetractionSectionPair.pointwise`, and `IsRetractionSectionPair.section_injective`: the AI renamed the bound variables to `ret` and `sec`. The meaning is unchanged.
- `IsRetractionSectionPair.section_injective`, `corestriction_surjective_completeInvariant`, `canonicalForm_to_section`, `section_to_canonicalForm`, and `canonicalForm_iff_section_of_completeInvariant`: the AI replaced each `simp` that does not close its goal with the `simp only [...]` call suggested by `simp?`.
- `isRetractionSectionPair_iff_rightInverse` and `isCompleteInvariant_iff_ker_eq`: the author chose these two equivalences with Mathlib's definitions, and the AI wrote their Lean statements and proofs.

All proofs are checked by Lean, and CI fails if any declaration depends on `sorry` or on an axiom other than `propext`, `Classical.choice`, and `Quot.sound`.
