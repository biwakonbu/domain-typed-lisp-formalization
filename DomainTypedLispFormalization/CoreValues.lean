import DomainTypedLispFormalization.CoreSyntax

namespace DomainTypedLispFormalization

inductive Value where
  | symbol (value : Name)
  | int (value : Int)
  | bool (value : Bool)
  | adt (ctor : Name) (fields : List Value)
  deriving Repr

abbrev Env := List (Name × Value)
abbrev GroundTuple := List Value

structure GroundFact where
  pred : Name
  args : GroundTuple
  deriving Repr

abbrev DerivedFacts := GroundFact -> Prop
abbrev Universe := Name -> Value -> Prop

end DomainTypedLispFormalization
