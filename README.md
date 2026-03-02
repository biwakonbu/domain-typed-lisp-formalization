# domain-typed-lisp-formalization

Lean 4 による `dtl` v0.6 コア意味論の形式化用リポジトリです。

## 対象
- 対象仕様: `dtl` language spec v0.6
- proof assistant: Lean 4.28.0
- upstream 実装: [biwakonbu/domain-typed-lisp](https://github.com/biwakonbu/domain-typed-lisp)

## 信頼境界
- 信頼するもの
  - parser
  - alias normalize
  - `resolve_program`
  - `check_program`
  - stratification
- 証明対象
  - stratified fixedpoint solver
  - `assert` evaluator
  - `defn Refine` evaluator

詳細:
- [trusted-boundary.md](./docs/trusted-boundary.md)
- [theorem-status.md](./docs/theorem-status.md)
- [semantics-core-v0.6.md](./docs/upstream/semantics-core-v0.6.md)
- [formalization-theorem-inventory.md](./docs/upstream/formalization-theorem-inventory.md)

## 優先順位
1. `fixedpoint_sound` / `fixedpoint_complete`
2. `assert_sound`
3. `refine_sound`

## 現在の状態
- Lean stub は `lake build` で compile する。
- theorem inventory の P0 セットは名前と依存先を固定済み。
- 証明本体は未着手で、現時点では `axiom` と placeholder 定義で骨組みのみを持つ。

## fixture
- `fixtures/semantics/negative-stratified/basic.dtl`
- `fixtures/semantics/match-pattern-sensitive/branch_sensitive.dtl`
- `fixtures/semantics/recursive-defn/list_allows.dtl`

## 使い方
```bash
bash ci/proof-smoke.sh
```

`lean-toolchain` により Lean 4.28.0 を pin しています。
