import DomainTypedLispFormalization.AssertSoundness

namespace DomainTypedLispFormalization

structure RefineObligation where
  name : Name
  vars : List (Name × DTLType)
  resultVar : Name
  goal : Formula
  body : Expr
  deriving Repr

def refineConclusion (callSemantics : ExprCallSemantics) (facts : DerivedFacts)
    (env : Env) (obligation : RefineObligation) : Prop :=
  match evalExpr callSemantics env obligation.body with
  | some (.bool true) =>
      evalFormula facts ((obligation.resultVar, .bool true) :: env) obligation.goal
  | some (.bool false) => True
  | _ => False

def RefineHolds (callSemantics : ExprCallSemantics) (facts : DerivedFacts)
    (carrier : TypedCarrier) (obligation : RefineObligation) : Prop :=
  ∀ env, env ∈ enumerateValuations carrier obligation.vars ->
    refineConclusion callSemantics facts env obligation

theorem refine_sound (callSemantics : ExprCallSemantics) (facts : DerivedFacts)
    (carrier : TypedCarrier) (obligation : RefineObligation) :
    RefineHolds callSemantics facts carrier obligation ->
    ∀ σ, AssignmentTyped carrier obligation.vars σ ->
      refineConclusion callSemantics facts (envOfAssignment obligation.vars σ) obligation := by
  intro hHolds σ hTyped
  exact hHolds (envOfAssignment obligation.vars σ)
    (valuation_enumeration_complete carrier obligation.vars σ hTyped)

end DomainTypedLispFormalization
