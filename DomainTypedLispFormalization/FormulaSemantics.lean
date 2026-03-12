import DomainTypedLispFormalization.CoreValues

namespace DomainTypedLispFormalization

inductive CallTarget where
  | relation
  | constructor
  | defn
  deriving Repr, DecidableEq

structure ExprCallSemantics where
  resolveCall : Name -> Option CallTarget
  evalRelation : Name -> List Value -> Option Bool
  evalConstructor : Name -> List Value -> Option Value
  evalDefn : Nat -> Name -> List Value -> Option Value

def unsupportedCallSemantics : ExprCallSemantics where
  resolveCall := fun _ => none
  evalRelation := fun _ _ => none
  evalConstructor := fun _ _ => none
  evalDefn := fun _ _ _ => none

def lookupEnv : Env -> Name -> Option Value
  | [], _ => none
  | (name, value) :: rest, target =>
      if name = target then some value else lookupEnv rest target

mutual
  def GroundTermInEnv (env : Env) : Term -> Prop
    | .var name => ∃ value, lookupEnv env name = some value
    | .symbol _ => True
    | .int _ => True
    | .bool _ => True
    | .ctor _ args => GroundTermsInEnv env args

  def GroundTermsInEnv (env : Env) : List Term -> Prop
    | [] => True
    | term :: rest => GroundTermInEnv env term ∧ GroundTermsInEnv env rest
end

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

def evalCall (callSemantics : ExprCallSemantics) (fuel : Nat) (name : Name) (args : List Value) :
    Option Value :=
  match callSemantics.resolveCall name with
  | some .relation => do
      let truth <- callSemantics.evalRelation name args
      some (.bool truth)
  | some .constructor => callSemantics.evalConstructor name args
  | some .defn => callSemantics.evalDefn fuel name args
  | none => none

mutual
  def evalExprFuel (callSemantics : ExprCallSemantics) (env : Env) : Nat -> Expr -> Option Value
    | 0, _ => none
    | _fuel + 1, .var name => lookupEnv env name
    | _fuel + 1, .symbol value => some (.symbol value)
    | _fuel + 1, .int value => some (.int value)
    | _fuel + 1, .bool value => some (.bool value)
    | fuel + 1, .call name args => do
        let values <- evalExprsFuel callSemantics env fuel args
        evalCall callSemantics fuel name values
    | fuel + 1, .letE bindings body => do
        let env' <- evalBindingsFuel callSemantics env fuel bindings
        evalExprFuel callSemantics env' fuel body
    | fuel + 1, .ifE cond thenBranch elseBranch => do
        let condValue <- evalExprFuel callSemantics env fuel cond
        match condValue with
        | .bool true => evalExprFuel callSemantics env fuel thenBranch
        | .bool false => evalExprFuel callSemantics env fuel elseBranch
        | _ => none
    | fuel + 1, .matchE scrutinee arms => do
        let value <- evalExprFuel callSemantics env fuel scrutinee
        evalMatchArmsFuel callSemantics env fuel value arms

  def evalExprsFuel (callSemantics : ExprCallSemantics) (env : Env) :
      Nat -> List Expr -> Option (List Value)
    | 0, _ => none
    | _fuel + 1, [] => some []
    | fuel + 1, expr :: rest => do
        let value <- evalExprFuel callSemantics env fuel expr
        let values <- evalExprsFuel callSemantics env fuel rest
        some (value :: values)

  def evalBindingsFuel (callSemantics : ExprCallSemantics) (env : Env) :
      Nat -> List (Name × Expr) -> Option Env
    | 0, _ => none
    | _fuel + 1, [] => some env
    | fuel + 1, (name, expr) :: rest => do
        let value <- evalExprFuel callSemantics env fuel expr
        evalBindingsFuel callSemantics ((name, value) :: env) fuel rest

  def evalMatchArmsFuel (callSemantics : ExprCallSemantics) (env : Env) :
      Nat -> Value -> List (Pattern × Expr) -> Option Value
    | 0, _, _ => none
    | _fuel + 1, _, [] => none
    | fuel + 1, value, (pattern, body) :: rest =>
        match matchPattern value pattern with
        | some bindings => evalExprFuel callSemantics (bindings ++ env) fuel body
        | none => evalMatchArmsFuel callSemantics env fuel value rest
end

noncomputable def evalExpr (callSemantics : ExprCallSemantics) (env : Env) (expr : Expr) :
    Option Value :=
  evalExprFuel callSemantics env (sizeOf expr + 1) expr

mutual
  theorem ground_substitution_closed {env : Env} :
      ∀ {term : Term}, GroundTermInEnv env term -> ∃ value, evalTerm env term = some value
    | .var _, hGround => by
        simpa [GroundTermInEnv, evalTerm] using hGround
    | .symbol value, _ => by
        exact ⟨.symbol value, rfl⟩
    | .int value, _ => by
        exact ⟨.int value, rfl⟩
    | .bool value, _ => by
        exact ⟨.bool value, rfl⟩
    | .ctor name args, hGround => by
        rcases ground_substitutions_closed hGround with ⟨values, hValues⟩
        exact ⟨.adt name values, by simp [evalTerm, hValues]⟩

  theorem ground_substitutions_closed {env : Env} :
      ∀ {terms : List Term}, GroundTermsInEnv env terms -> ∃ values, evalTerms env terms = some values
    | [], _ => by
        exact ⟨[], rfl⟩
    | term :: rest, hGround => by
        rcases hGround with ⟨hTerm, hRest⟩
        rcases ground_substitution_closed hTerm with ⟨value, hValue⟩
        rcases ground_substitutions_closed hRest with ⟨values, hValues⟩
        exact ⟨value :: values, by simp [evalTerms, hValue, hValues]⟩
end

theorem formula_eval_deterministic (facts : DerivedFacts) (env : Env) (formula : Formula) :
    evalFormula facts env formula ↔ evalFormula facts env formula := Iff.rfl

theorem pattern_match_deterministic {value : Value} {arms : List (Pattern × Expr)} {lhs rhs : Expr} :
    selectMatchArm value arms = some lhs ->
    selectMatchArm value arms = some rhs ->
    lhs = rhs := by
  intro hLeft hRight
  rw [hLeft] at hRight
  injection hRight

theorem expr_eval_deterministic {callSemantics : ExprCallSemantics} {env : Env}
    {expr : Expr} {lhs rhs : Value} :
    evalExpr callSemantics env expr = some lhs ->
    evalExpr callSemantics env expr = some rhs ->
    lhs = rhs := by
  intro hLeft hRight
  rw [hLeft] at hRight
  injection hRight

end DomainTypedLispFormalization
