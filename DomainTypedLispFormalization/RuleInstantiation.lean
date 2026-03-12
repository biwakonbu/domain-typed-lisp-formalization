import DomainTypedLispFormalization.FormulaSemantics

namespace DomainTypedLispFormalization

abbrev GroundDatabase := List GroundFact

mutual
  def valueEq : Value -> Value -> Bool
    | .symbol lhs, .symbol rhs => lhs == rhs
    | .int lhs, .int rhs => lhs == rhs
    | .bool lhs, .bool rhs => lhs == rhs
    | .adt lhsCtor lhsFields, .adt rhsCtor rhsFields =>
        lhsCtor == rhsCtor && valuesEq lhsFields rhsFields
    | _, _ => false

  def valuesEq : List Value -> List Value -> Bool
    | [], [] => true
    | lhs :: lhsRest, rhs :: rhsRest => valueEq lhs rhs && valuesEq lhsRest rhsRest
    | _, _ => false
end

def groundFactEq (lhs rhs : GroundFact) : Bool :=
  lhs.pred == rhs.pred && valuesEq lhs.args rhs.args

def dbContains (db : GroundDatabase) (fact : GroundFact) : Bool :=
  db.any fun candidate => groundFactEq candidate fact

def factsOfDatabase (db : GroundDatabase) : DerivedFacts :=
  fun fact => dbContains db fact = true

def atomToFormula (atom : Atom) : Formula :=
  .pred atom.pred atom.terms

def flattenFormulaAux : Bool -> Formula -> List Atom × List Atom
  | _negated, .triv => ([], [])
  | false, .pred name args => ([{ pred := name, terms := args }], [])
  | true, .pred name args => ([], [{ pred := name, terms := args }])
  | negated, .andF goals =>
      goals.foldr
        (fun goal (positives, negatives) =>
          let (positives', negatives') := flattenFormulaAux negated goal
          (positives' ++ positives, negatives' ++ negatives))
        ([], [])
  | negated, .notF goal => flattenFormulaAux (!negated) goal

def flattenFormula (formula : Formula) : List Atom × List Atom :=
  flattenFormulaAux false formula

mutual
  def termVars : Term -> List Name
    | .var name => [name]
    | .symbol _ => []
    | .int _ => []
    | .bool _ => []
    | .ctor _ args => termsVars args

  def termsVars : List Term -> List Name
    | [] => []
    | term :: rest => termVars term ++ termsVars rest
end

def atomVars (atom : Atom) : List Name :=
  termsVars atom.terms

def namesBoundByAtoms (names : List Name) (atoms : List Atom) : Prop :=
  ∀ name, name ∈ names -> ∃ atom, atom ∈ atoms ∧ name ∈ atomVars atom

def RuleWellFormed (rule : Rule) : Prop :=
  let (positives, negatives) := flattenFormula rule.body
  namesBoundByAtoms (atomVars rule.head) positives ∧
    ∀ atom, atom ∈ negatives -> namesBoundByAtoms (atomVars atom) positives

def relationTuples : GroundDatabase -> Name -> List GroundTuple
  | [], _ => []
  | fact :: rest, pred =>
      if fact.pred = pred then fact.args :: relationTuples rest pred else relationTuples rest pred

mutual
  def unifyTerm : Term -> Value -> Env -> Option Env
    | .var name, value, env =>
        match lookupEnv env name with
        | some bound => if valueEq bound value then some env else none
        | none => some ((name, value) :: env)
    | .symbol expected, .symbol actual, env =>
        if expected = actual then some env else none
    | .symbol _, _, _ => none
    | .int expected, .int actual, env =>
        if expected = actual then some env else none
    | .int _, _, _ => none
    | .bool expected, .bool actual, env =>
        if expected = actual then some env else none
    | .bool _, _, _ => none
    | .ctor expected args, .adt actual fields, env =>
        if expected = actual then unifyTerms args fields env else none
    | .ctor _ _, _, _ => none

  def unifyTerms : List Term -> List Value -> Env -> Option Env
    | [], [], env => some env
    | term :: terms, value :: values, env => do
        let env' <- unifyTerm term value env
        unifyTerms terms values env'
    | _, _, _ => none
end

def unifyAtom (atom : Atom) (tuple : GroundTuple) (env : Env) : Option Env :=
  unifyTerms atom.terms tuple env

def extendAssignmentsWithAtom (db : GroundDatabase) (envs : List Env) (atom : Atom) : List Env :=
  envs.flatMap fun env =>
    (relationTuples db atom.pred).filterMap fun tuple => unifyAtom atom tuple env

def positiveAssignments (db : GroundDatabase) (positives : List Atom) : List Env :=
  positives.foldl (extendAssignmentsWithAtom db) [[]]

def passesNegativeFilter (db : GroundDatabase) (negatives : List Atom) (env : Env) : Bool :=
  negatives.all fun atom =>
    match evalTerms env atom.terms with
    | some tuple => dbContains db { pred := atom.pred, args := tuple } == false
    | none => false

def filterNegativeAssignments (db : GroundDatabase) (negatives : List Atom) (envs : List Env) :
    List Env :=
  envs.filter fun env => passesNegativeFilter db negatives env

def instantiateHead (env : Env) (head : Atom) : Option GroundFact := do
  let args <- evalTerms env head.terms
  some { pred := head.pred, args := args }

def instantiateRule (db : GroundDatabase) (rule : Rule) : List GroundFact :=
  let (positives, negatives) := flattenFormula rule.body
  let filtered := filterNegativeAssignments db negatives (positiveAssignments db positives)
  filtered.filterMap fun env => instantiateHead env rule.head

def NegativeConditionsHold (db : GroundDatabase) (rule : Rule) (env : Env) : Prop :=
  ∀ atom, atom ∈ (flattenFormula rule.body).2 ->
    evalFormula (factsOfDatabase db) env (.notF (atomToFormula atom))

def RuleInstantiationWitness (db : GroundDatabase) (rule : Rule) (env : Env)
    (fact : GroundFact) : Prop :=
  let (positives, negatives) := flattenFormula rule.body
  env ∈ positiveAssignments db positives ∧
    passesNegativeFilter db negatives env = true ∧
    instantiateHead env rule.head = some fact

theorem mem_filterNegativeAssignments {db : GroundDatabase} {negatives : List Atom}
    {envs : List Env} {env : Env} :
    env ∈ filterNegativeAssignments db negatives envs ↔
      env ∈ envs ∧ passesNegativeFilter db negatives env = true := by
  simp [filterNegativeAssignments]

theorem negative_literal_filter_sound {db : GroundDatabase} {rule : Rule} {envs : List Env}
    {env : Env} (_hWellFormed : RuleWellFormed rule)
    (hEnv : env ∈ filterNegativeAssignments db (flattenFormula rule.body).2 envs) :
    NegativeConditionsHold db rule env := by
  intro atom hAtom
  have hPass : passesNegativeFilter db (flattenFormula rule.body).2 env = true :=
    (mem_filterNegativeAssignments.mp hEnv).2
  have hEach :=
    (List.all_eq_true.mp hPass) atom hAtom
  cases hEval : evalTerms env atom.terms with
  | none =>
      simp [hEval] at hEach
  | some tuple =>
      simp [atomToFormula, evalFormula, factsOfDatabase, hEval] at hEach ⊢
      exact hEach

theorem rule_instantiation_sound {db : GroundDatabase} {rule : Rule} {fact : GroundFact}
    (hWellFormed : RuleWellFormed rule) :
    fact ∈ instantiateRule db rule ->
      ∃ env, RuleInstantiationWitness db rule env fact ∧ NegativeConditionsHold db rule env := by
  intro hFact
  classical
  rcases List.mem_filterMap.mp hFact with ⟨env, hFiltered, hHead⟩
  have hFilter :
      env ∈ filterNegativeAssignments db (flattenFormula rule.body).2
        (positiveAssignments db (flattenFormula rule.body).1) := by
    simpa [instantiateRule] using hFiltered
  have hWitness : RuleInstantiationWitness db rule env fact := by
    have hMem := mem_filterNegativeAssignments.mp hFilter
    exact ⟨hMem.1, hMem.2, hHead⟩
  exact ⟨env, hWitness, negative_literal_filter_sound hWellFormed hFilter⟩

theorem rule_instantiation_complete {db : GroundDatabase} {rule : Rule} {env : Env}
    {fact : GroundFact} :
    RuleInstantiationWitness db rule env fact ->
      fact ∈ instantiateRule db rule := by
  intro hWitness
  classical
  rcases hWitness with ⟨hPositive, hNegative, hHead⟩
  apply List.mem_filterMap.mpr
  refine ⟨env, ?_, hHead⟩
  have hFilter :
      env ∈ filterNegativeAssignments db (flattenFormula rule.body).2
        (positiveAssignments db (flattenFormula rule.body).1) := by
    exact mem_filterNegativeAssignments.mpr ⟨hPositive, hNegative⟩
  simpa [instantiateRule] using hFilter

end DomainTypedLispFormalization
