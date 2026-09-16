# CanonicalForms

同値関係に対する不変量と標準形のLean 4による形式化．

[![Build Status](https://github.com/ys-math/CanonicalForms/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/ys-math/CanonicalForms/actions/workflows/lean_action_ci.yml)

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

## AIの利用について

本プロジェクトでは, AIモデルを計画・ドキュメント作成・注釈付け・ビルドとCIの設定（`scripts/CheckAxioms.lean` を含む）の作業に利用しています. 数学的な主張及びそのLeanによる証明は, 以下の変更を除き著者自身が記述し検証しています. 以下の変更は著者の依頼に基づきClaude Code（Claude Opus 5）が行いました.

- `canonicalFormOfCompleteInvariant_exists`（命題4）：主張を著者が与えた主張に置き換えました. 新しい主張は写像 `I : α → β` を取り, `s'` が `corestriction I` のセクションであることを述べます. 証明はAIが新しい主張に合わせて修正しました. また, AIが `docs/theory_en.tex` と `docs/theory_ja.tex` の命題4に `I` が完全な不変量であるという仮定を追加し, 両方のPDFを再生成しました.
- `corestriction_surjective_completeInvariant`（命題3）：著者の指定に従い, `let` の代わりに `corestriction` を用いて主張を書き直しました. AIが `corestriction` の定義をこの定理の前に移動し, 証明を修正しました.
- `IsRetractionSectionPair`, `IsRetractionSectionPair.pointwise`, `IsRetractionSectionPair.section_injective`：AIが束縛変数の名前を `ret` と `sec` に変更しました. 意味は変わりません.
- `IsRetractionSectionPair.section_injective`, `corestriction_surjective_completeInvariant`, `canonicalForm_to_section`, `section_to_canonicalForm`, `canonicalForm_iff_section_of_completeInvariant`：ゴールを閉じない `simp` を, AIが `simp?` の提案する `simp only [...]` に置き換えました.
- `isRetractionSectionPair_iff_rightInverse`, `isCompleteInvariant_iff_ker_eq`：Mathlibの定義との2つの同値性は著者が選び, Leanによる主張と証明はAIが記述しました.

すべての証明はLeanによって検査されています. また, `sorry` または `propext`, `Classical.choice`, `Quot.sound` 以外の公理に依存する宣言が一つでもあるとCIは失敗します.

---

## ライセンス

[Apache 2.0](LICENSE)