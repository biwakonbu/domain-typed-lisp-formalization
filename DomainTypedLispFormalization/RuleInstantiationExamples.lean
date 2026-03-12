import DomainTypedLispFormalization.RuleInstantiation
import DomainTypedLispFormalization.ConstructorNormalization

namespace DomainTypedLispFormalization

def edgeDb : GroundDatabase := Id.run do
  pure [GroundFact.mk "edge" [.symbol "a"]]

def reachRule : Rule := Id.run do
  pure <| Rule.mk (Atom.mk "reachable" [.var "x"]) (.pred "edge" [.var "x"])

theorem reachWitness :
    RuleInstantiationWitness edgeDb reachRule [("x", Value.symbol "a")]
      (GroundFact.mk "reachable" [.symbol "a"]) := by
  simp [RuleInstantiationWitness, reachRule, flattenFormula, flattenFormulaAux]
  constructor
  · change [("x", Value.symbol "a")] ∈ extendAssignmentsWithAtom edgeDb [[]] (Atom.mk "edge" [.var "x"])
    apply List.mem_flatMap.mpr
    refine ⟨[], by simp, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨[Value.symbol "a"], ?_, ?_⟩
    · simp [edgeDb, relationTuples]
    · simp [unifyAtom, unifyTerms, unifyTerm, lookupEnv]
  · constructor
    · simp [passesNegativeFilter]
    · simp [instantiateHead, evalTerm, evalTerms, lookupEnv]

example : GroundFact.mk "reachable" [.symbol "a"] ∈ instantiateRule edgeDb reachRule := by
  exact rule_instantiation_complete reachWitness

def negativeDb : GroundDatabase := Id.run do
  pure
    [ GroundFact.mk "p" [.symbol "a"]
    , GroundFact.mk "p" [.symbol "b"]
    , GroundFact.mk "blocked" [.symbol "b"]
    ]

def qRule : Rule := Id.run do
  pure <| Rule.mk (Atom.mk "q" [.var "x"])
    (.andF [.pred "p" [.var "x"], .notF (.pred "blocked" [.var "x"])])

theorem qRuleWellFormed : RuleWellFormed qRule := by
  constructor
  · intro name hName
    have hPositive : Atom.mk "p" [Term.var "x"] ∈ (flattenFormula qRule.body).1 := by
      simp [qRule, flattenFormula, flattenFormulaAux]
    simp [qRule, atomVars, termVars, termsVars] at hName
    subst hName
    exact ⟨Atom.mk "p" [Term.var "x"], hPositive, by simp [atomVars, termVars, termsVars]⟩
  · intro atom hAtom name hName
    have hAtomEq : atom = Atom.mk "blocked" [Term.var "x"] := by
      simpa [qRule, flattenFormula, flattenFormulaAux] using hAtom
    subst hAtomEq
    have hPositive : Atom.mk "p" [Term.var "x"] ∈ (flattenFormula qRule.body).1 := by
      simp [qRule, flattenFormula, flattenFormulaAux]
    simp [atomVars, termVars, termsVars] at hName
    subst hName
    exact ⟨Atom.mk "p" [Term.var "x"], hPositive, by simp [atomVars, termVars, termsVars]⟩

theorem qWitnessA :
    RuleInstantiationWitness negativeDb qRule [("x", Value.symbol "a")]
      (GroundFact.mk "q" [.symbol "a"]) := by
  simp [RuleInstantiationWitness, qRule, flattenFormula, flattenFormulaAux]
  constructor
  · change [("x", Value.symbol "a")] ∈ extendAssignmentsWithAtom negativeDb [[]] (Atom.mk "p" [.var "x"])
    apply List.mem_flatMap.mpr
    refine ⟨[], by simp, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨[Value.symbol "a"], ?_, ?_⟩
    · simp [negativeDb, relationTuples]
    · simp [unifyAtom, unifyTerms, unifyTerm, lookupEnv]
  · constructor
    · simp [negativeDb, passesNegativeFilter, evalTerm, evalTerms, lookupEnv,
        dbContains, groundFactEq, valueEq, valuesEq]
    · simp [instantiateHead, evalTerm, evalTerms, lookupEnv]

example : GroundFact.mk "q" [.symbol "a"] ∈ instantiateRule negativeDb qRule := by
  exact rule_instantiation_complete qWitnessA

example : NegativeConditionsHold negativeDb qRule [("x", Value.symbol "a")] := by
  apply negative_literal_filter_sound qRuleWellFormed
  rcases qWitnessA with ⟨hPositive, hNegative, _hHead⟩
  exact mem_filterNegativeAssignments.mpr ⟨hPositive, hNegative⟩

example : GroundFact.mk "q" [.symbol "b"] ∉ instantiateRule negativeDb qRule := by
  intro hFact
  rcases rule_instantiation_sound qRuleWellFormed hFact with ⟨env, hWitness, _hNegCond⟩
  rcases hWitness with ⟨hPositive, hNegative, hHead⟩
  have hCases : env = [("x", Value.symbol "a")] ∨ env = [("x", Value.symbol "b")] := by
    simpa [qRule, flattenFormula, flattenFormulaAux, positiveAssignments, extendAssignmentsWithAtom,
      negativeDb, relationTuples, unifyAtom, unifyTerms, unifyTerm, lookupEnv, valueEq,
      valuesEq] using hPositive
  cases hCases with
  | inl hA =>
      rw [hA] at hHead
      simp [qRule, instantiateHead, evalTerm, evalTerms, lookupEnv] at hHead
  | inr hB =>
      rw [hB] at hNegative
      simp [qRule, flattenFormulaAux, passesNegativeFilter, negativeDb,
        evalTerm, evalTerms, lookupEnv, dbContains, groundFactEq, valueEq, valuesEq] at hNegative

example :
    ∃ env, RuleInstantiationWitness negativeDb qRule env (GroundFact.mk "q" [.symbol "a"]) ∧
      NegativeConditionsHold negativeDb qRule env := by
  exact rule_instantiation_sound qRuleWellFormed (rule_instantiation_complete qWitnessA)

def aliasCanonicalize : Name -> Name
  | "閲覧" => "read"
  | name => name

def aliasTerm : Term := Id.run do
  pure <| .ctor "閲覧" []

example :
    evalTerm (normalizeEnvConstructors aliasCanonicalize [])
        (normalizeTermConstructors aliasCanonicalize aliasTerm) =
      some (.adt "read" []) := by
  simp [aliasCanonicalize, aliasTerm, normalizeEnvConstructors,
    normalizeTermConstructors, evalTerm, evalTerms]

example :
    evalTerm (normalizeEnvConstructors aliasCanonicalize [])
        (normalizeTermConstructors aliasCanonicalize aliasTerm) =
      Option.map (normalizeValueConstructors aliasCanonicalize) (evalTerm [] aliasTerm) := by
  simpa using constructor_normalization_preserves_value aliasCanonicalize [] aliasTerm

end DomainTypedLispFormalization
