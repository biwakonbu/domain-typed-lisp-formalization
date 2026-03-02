import DomainTypedLispFormalization.AssertSoundness

namespace DomainTypedLispFormalization

structure RefineObligation where
  name : Name
  vars : List (Name × DTLType)
  resultVar : Name
  goal : Formula
  body : Expr
  deriving Repr

def RefineHolds (_facts : DerivedFacts) (_universe : Universe) (_obligation : RefineObligation) :
    Prop := True

axiom refine_sound : Prop

end DomainTypedLispFormalization
