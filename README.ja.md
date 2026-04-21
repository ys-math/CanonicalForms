# CanonicalForms

同値関係に対する不変量と標準形のLean 4による形式化．

[![Build Status](https://github.com/ys-math/CanonicalForms/actions/workflows/ci.yml/badge.svg)](https://github.com/ys-math/CanonicalForms/actions)

---

## 内容

型 `α` 上の同値関係 `∼` に対して以下の概念を形式化する.

写像 `f : α → β` が同値な元を等しい元に写すとき, `f` を `∼` の**不変量**という. さらにその逆も成り立つとき`f` を`∼` の**完全な不変量**という.　`∼` の不変量 `C : α → α` であって, すべての `x` に対して `x ∼ C x` を満たすものを`∼` の**標準形**という. `C(α)` を`∼`の**骨格**または**完全代表系**という.

主要な結果として, レトラクション-セクションペアによる標準形の特徴付け及び選択公理を仮定した上での完全な不変量によって定まる標準形が存在することの証明を含む.

自然言語による証明は以下のPDFを参照してください.

- 英語版：[`docs/theory_en.pdf`](docs/theory_en.pdf)
- 日本語版：[`docs/theory_ja.pdf`](docs/theory_ja.pdf)

---

## リポジトリ構造

```
CanonicalForms/
├── CanonicalForms/
│   ├── Basic.lean                 # IsInvariant, IsCompleteInvariant
│   ├── CanonicalForm.lean         # IsCanonicalForm, skeleton
│   └── Existence.lean             # 存在定理（AC）
└── docs/
    ├── theory_en.pdf              # 自然言語による証明（英語）
    ├── theory_en.tex
    ├── theory_ja.pdf              # 自然言語による証明（日本語）
    └── theory_ja.tex
```

---

## 参考文献

- [Mathlib4: Setoid](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Setoid/Basic.html)
- [Mathlib4: Quotient](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quotient)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [The Lean Language Reference/Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/#quotients)

---

## ライセンス

[Apache 2.0](LICENSE)