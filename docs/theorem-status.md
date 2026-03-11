# theorem status

| theorem | phase | status | note |
| --- | --- | --- | --- |
| `fixedpoint_step_monotone` | P0 | proved | abstract carrier fixedpoint |
| `fixedpoint_least_model_exists` | P0 | proved | abstract carrier fixedpoint |
| `fixedpoint_sound` | P0 | proved | abstract carrier fixedpoint |
| `fixedpoint_complete` | P0 | proved | abstract carrier fixedpoint |
| `formula_eval_deterministic` | P1 | proved | current core evaluator |
| `pattern_match_deterministic` | P1 | proved | first-match arm selection |
| `expr_eval_deterministic` | P1 | proved | current evaluator; `call` is unsupported |
| `assert_sound` | P2 | stub | declaration only |
| `refine_sound` | P2 | stub | declaration only |

## 補助補題
- `ground_substitution_closed`: stub
- `negative_literal_filter_sound`: stub
- `rule_instantiation_sound`: stub
- `rule_instantiation_complete`: stub
- `constructor_normalization_preserves_value`: stub
- `valuation_enumeration_complete`: proved
