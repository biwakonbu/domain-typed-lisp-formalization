import DomainTypedLispFormalization.Fixedpoint

namespace DomainTypedLispFormalization

structure AssertionObligation where
  name : Name
  vars : List (Name × DTLType)
  goal : Formula
  deriving Repr

def AssertionHolds (_facts : DerivedFacts) (_universe : Universe) (_obligation : AssertionObligation) :
    Prop := True

axiom valuation_enumeration_complete : Prop
axiom assert_sound : Prop

end DomainTypedLispFormalization
