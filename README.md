# CanonicalForms

A Lean 4 formalization of invariants and canonical forms for equivalence relations.

[![Build Status](https://github.com/ys-math/CanonicalForms/actions/workflows/ci.yml/badge.svg)](https://github.com/ys-math/CanonicalForms/actions)

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

## License

[Apache 2.0](LICENSE)