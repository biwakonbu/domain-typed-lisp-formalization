# theorem status

| theorem | phase | status | note |
| --- | --- | --- | --- |
| `fixedpoint_step_monotone` | P0 | proved | abstract carrier fixedpoint |
| `fixedpoint_least_model_exists` | P0 | proved | abstract carrier fixedpoint |
| `fixedpoint_sound` | P0 | proved | abstract carrier fixedpoint |
| `fixedpoint_complete` | P0 | proved | abstract carrier fixedpoint |
| `formula_eval_deterministic` | P1 | proved | current core evaluator |
| `pattern_match_deterministic` | P1 | proved | first-match arm selection |
| `expr_eval_deterministic` | P1 | proved | abstract call semantics 付き evaluator |
| `assert_sound` | P2 | proved | finite typed carrier 上の obligation evaluator |
| `refine_sound` | P2 | proved | `evalExpr` / `evalFormula` 接続済み |

## 補助補題
- `ground_substitution_closed`: proved
- `negative_literal_filter_sound`: proved
- `rule_instantiation_sound`: proved
- `rule_instantiation_complete`: proved
- `constructor_normalization_preserves_value`: proved
- `valuation_enumeration_complete`: proved
