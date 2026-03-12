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
- abstract fixedpoint semantics の P0 4 定理は Lean theorem として実装済み。
- finite typed carrier 上の `valuation_enumeration_complete` は Lean theorem として実装済み。
- `Formula` / `Pattern` / `Expr` の core evaluator と P1 determinism theorem を実装済み。
- `Expr.call` は abstract call semantics で relation / constructor / defn call へ分岐する。
- `assert_sound` / `refine_sound` は finite typed carrier 上の obligation evaluator として theorem 化済み。
- rule instantiation / constructor normalization の helper 定理
  (`ground_substitution_closed`, `negative_literal_filter_sound`,
  `rule_instantiation_sound`, `rule_instantiation_complete`,
  `constructor_normalization_preserves_value`) は theorem 化済み。
- `lake build` / `bash ci/proof-smoke.sh` で `RuleInstantiationExamples` を含めて compile する。

## P0 完了済み定理
- `fixedpoint_step_monotone`
- `fixedpoint_least_model_exists`
- `fixedpoint_sound`
- `fixedpoint_complete`

## fixture
- `fixtures/semantics/negative-stratified/basic.dtl`
- `fixtures/semantics/match-pattern-sensitive/branch_sensitive.dtl`
- `fixtures/semantics/recursive-defn/list_allows.dtl`

## 使い方
```bash
bash ci/proof-smoke.sh
```

`lean-toolchain` により Lean 4.28.0 を pin しています。
