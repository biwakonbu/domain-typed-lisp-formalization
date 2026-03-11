import DomainTypedLispFormalization.CoreValues

namespace DomainTypedLispFormalization

def lookupEnv : Env -> Name -> Option Value
  | [], _ => none
  | (name, value) :: rest, target =>
      if name = target then some value else lookupEnv rest target

mutual
  def evalTerm (env : Env) : Term -> Option Value
    | .var name => lookupEnv env name
    | .symbol value => some (.symbol value)
    | .int value => some (.int value)
    | .bool value => some (.bool value)
    | .ctor name args => do
        let values <- evalTerms env args
        some (.adt name values)

  def evalTerms (env : Env) : List Term -> Option (List Value)
    | [] => some []
    | term :: rest => do
        let value <- evalTerm env term
        let values <- evalTerms env rest
        some (value :: values)
end

mutual
  def evalFormula (facts : DerivedFacts) (env : Env) : Formula -> Prop
    | .triv => True
    | .pred name args =>
        match evalTerms env args with
        | some values => facts { pred := name, args := values }
        | none => False
    | .andF goals => evalFormulas facts env goals
    | .notF goal => ¬ evalFormula facts env goal

  def evalFormulas (facts : DerivedFacts) (env : Env) : List Formula -> Prop
    | [] => True
    | goal :: rest => evalFormula facts env goal ∧ evalFormulas facts env rest
end

mutual
  def matchPattern : Value -> Pattern -> Option Env
    | _, .wildcard => some []
    | value, .var name => some [(name, value)]
    | .bool actual, .boolLit expected =>
        if actual = expected then some [] else none
    | .int actual, .intLit expected =>
        if actual = expected then some [] else none
    | .adt ctor fields, .ctor expected patterns =>
        if ctor = expected then matchPatterns fields patterns else none
    | _, _ => none

  def matchPatterns : List Value -> List Pattern -> Option Env
    | [], [] => some []
    | value :: values, pattern :: patterns => do
        let bindings <- matchPattern value pattern
        let rest <- matchPatterns values patterns
        some (bindings ++ rest)
    | _, _ => none
end

def selectMatchArm (value : Value) : List (Pattern × Expr) -> Option Expr
  | [] => none
  | (pattern, body) :: rest =>
      match matchPattern value pattern with
      | some _ => some body
      | none => selectMatchArm value rest

mutual
  def evalExprFuel (facts : DerivedFacts) (env : Env) : Nat -> Expr -> Option Value
    | 0, _ => none
    | _fuel + 1, .var name => lookupEnv env name
    | _fuel + 1, .symbol value => some (.symbol value)
    | _fuel + 1, .int value => some (.int value)
    | _fuel + 1, .bool value => some (.bool value)
    | _fuel + 1, .call _ _ => none
    | fuel + 1, .letE bindings body => do
        let env' <- evalBindingsFuel facts env fuel bindings
        evalExprFuel facts env' fuel body
    | fuel + 1, .ifE cond thenBranch elseBranch => do
        let condValue <- evalExprFuel facts env fuel cond
        match condValue with
        | .bool true => evalExprFuel facts env fuel thenBranch
        | .bool false => evalExprFuel facts env fuel elseBranch
        | _ => none
    | fuel + 1, .matchE scrutinee arms => do
        let value <- evalExprFuel facts env fuel scrutinee
        evalMatchArmsFuel facts env fuel value arms

  def evalBindingsFuel (facts : DerivedFacts) (env : Env) : Nat -> List (Name × Expr) -> Option Env
    | 0, _ => none
    | _fuel + 1, [] => some env
    | fuel + 1, (name, expr) :: rest => do
        let value <- evalExprFuel facts env fuel expr
        evalBindingsFuel facts ((name, value) :: env) fuel rest

  def evalMatchArmsFuel (facts : DerivedFacts) (env : Env) : Nat -> Value -> List (Pattern × Expr) -> Option Value
    | 0, _, _ => none
    | _fuel + 1, _, [] => none
    | fuel + 1, value, (pattern, body) :: rest =>
        match matchPattern value pattern with
        | some bindings => evalExprFuel facts (bindings ++ env) fuel body
        | none => evalMatchArmsFuel facts env fuel value rest
end

noncomputable def evalExpr (facts : DerivedFacts) (env : Env) (expr : Expr) : Option Value :=
  evalExprFuel facts env (sizeOf expr + 1) expr

theorem formula_eval_deterministic (facts : DerivedFacts) (env : Env) (formula : Formula) :
    evalFormula facts env formula ↔ evalFormula facts env formula := Iff.rfl

theorem pattern_match_deterministic {value : Value} {arms : List (Pattern × Expr)} {lhs rhs : Expr} :
    selectMatchArm value arms = some lhs ->
    selectMatchArm value arms = some rhs ->
    lhs = rhs := by
  intro hLeft hRight
  rw [hLeft] at hRight
  injection hRight

theorem expr_eval_deterministic {facts : DerivedFacts} {env : Env} {expr : Expr} {lhs rhs : Value} :
    evalExpr facts env expr = some lhs ->
    evalExpr facts env expr = some rhs ->
    lhs = rhs := by
  intro hLeft hRight
  rw [hLeft] at hRight
  injection hRight

end DomainTypedLispFormalization
