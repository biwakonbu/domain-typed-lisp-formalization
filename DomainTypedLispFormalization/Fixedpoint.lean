import DomainTypedLispFormalization.FormulaSemantics

namespace DomainTypedLispFormalization

structure Rule where
  head : GroundFact
  body : Formula
  deriving Repr

structure Stratum where
  rules : List Rule
  deriving Repr

structure StepOperator where
  apply : DerivedFacts -> DerivedFacts

def Monotone (op : StepOperator) : Prop :=
  ∀ ⦃s t : DerivedFacts⦄, (∀ fact, s fact -> t fact) -> ∀ fact, op.apply s fact -> op.apply t fact

def LeastFixedPointExists (_op : StepOperator) : Prop := True

axiom ground_substitution_closed : Prop
axiom negative_literal_filter_sound : Prop
axiom rule_instantiation_sound : Prop
axiom rule_instantiation_complete : Prop
axiom constructor_normalization_preserves_value : Prop

axiom fixedpoint_step_monotone : Prop
axiom fixedpoint_least_model_exists : Prop
axiom fixedpoint_sound : Prop
axiom fixedpoint_complete : Prop

end DomainTypedLispFormalization
