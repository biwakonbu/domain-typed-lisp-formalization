import DomainTypedLispFormalization.FormulaSemantics

namespace DomainTypedLispFormalization

def normalizeValueConstructors (normalizeCtorName : Name -> Name) : Value -> Value
  | .symbol value => .symbol value
  | .int value => .int value
  | .bool value => .bool value
  | .adt ctor fields =>
      .adt (normalizeCtorName ctor) (fields.map (normalizeValueConstructors normalizeCtorName))

def normalizeTermConstructors (normalizeCtorName : Name -> Name) : Term -> Term
  | .var name => .var name
  | .symbol value => .symbol value
  | .int value => .int value
  | .bool value => .bool value
  | .ctor ctor args =>
      .ctor (normalizeCtorName ctor) (args.map (normalizeTermConstructors normalizeCtorName))

def normalizeEnvConstructors (normalizeCtorName : Name -> Name) : Env -> Env :=
  List.map fun (name, value) => (name, normalizeValueConstructors normalizeCtorName value)

theorem lookupEnv_normalizeEnv (normalizeCtorName : Name -> Name) (env : Env) (name : Name) :
    lookupEnv (normalizeEnvConstructors normalizeCtorName env) name =
      Option.map (normalizeValueConstructors normalizeCtorName) (lookupEnv env name) := by
  induction env with
  | nil =>
      simp [lookupEnv, normalizeEnvConstructors]
  | cons entry rest ih =>
      rcases entry with ⟨entryName, entryValue⟩
      by_cases hEq : entryName = name
      · simp [lookupEnv, normalizeEnvConstructors, hEq]
      · simpa [lookupEnv, normalizeEnvConstructors, hEq] using ih

mutual
  theorem constructor_normalization_preserves_value (normalizeCtorName : Name -> Name) (env : Env) :
      ∀ term,
        evalTerm (normalizeEnvConstructors normalizeCtorName env)
            (normalizeTermConstructors normalizeCtorName term) =
          Option.map (normalizeValueConstructors normalizeCtorName) (evalTerm env term)
    | .var name => by
        simpa [normalizeTermConstructors, evalTerm] using
          lookupEnv_normalizeEnv normalizeCtorName env name
    | .symbol value => by
        simp [normalizeTermConstructors, normalizeValueConstructors, evalTerm]
    | .int value => by
        simp [normalizeTermConstructors, normalizeValueConstructors, evalTerm]
    | .bool value => by
        simp [normalizeTermConstructors, normalizeValueConstructors, evalTerm]
    | .ctor ctor args => by
        cases hArgs : evalTerms env args with
        | none =>
            simp [normalizeTermConstructors, evalTerm, hArgs,
              constructor_normalization_preserves_values]
        | some values =>
            have hNorm :
                evalTerms (normalizeEnvConstructors normalizeCtorName env)
                    (List.map (normalizeTermConstructors normalizeCtorName) args) =
                  some (List.map (normalizeValueConstructors normalizeCtorName) values) := by
              simpa [hArgs] using constructor_normalization_preserves_values normalizeCtorName env args
            simp [normalizeTermConstructors, normalizeValueConstructors, evalTerm, hArgs]
            rw [hNorm]
            simp

  theorem constructor_normalization_preserves_values (normalizeCtorName : Name -> Name) (env : Env) :
      ∀ terms,
        evalTerms (normalizeEnvConstructors normalizeCtorName env)
            (terms.map (normalizeTermConstructors normalizeCtorName)) =
          Option.map (List.map (normalizeValueConstructors normalizeCtorName)) (evalTerms env terms)
    | [] => by
        simp [evalTerms]
    | term :: terms => by
        have hHead := constructor_normalization_preserves_value normalizeCtorName env term
        have hTail := constructor_normalization_preserves_values normalizeCtorName env terms
        cases hEvalTerm : evalTerm env term <;>
          cases hEvalTerms : evalTerms env terms <;>
            simp [evalTerms, hHead, hTail, hEvalTerm, hEvalTerms]
end

end DomainTypedLispFormalization
