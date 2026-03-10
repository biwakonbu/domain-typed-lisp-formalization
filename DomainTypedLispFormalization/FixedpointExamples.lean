import DomainTypedLispFormalization.Fixedpoint

namespace DomainTypedLispFormalization

inductive ToyFact where
  | a
  | b
  deriving DecidableEq, Repr

def toyDerive : FactSet ToyFact → FactSet ToyFact := fun s x =>
  match x with
  | .a => true
  | .b => s ToyFact.a

def toyOp : ClosureOperator ToyFact where
  carrier := [ToyFact.a, ToyFact.b]
  carrier_nodup := by simp
  derive := toyDerive
  derive_bounded := by
    intro _ x hx
    cases x <;> simp
  derive_monotone := by
    intro s t hsub x hx
    cases x with
    | a =>
        rfl
    | b =>
        exact hsub ToyFact.a hx

example : IsFixedPoint toyOp (lfp toyOp) := fixedpoint_sound toyOp

example : ∀ t, IsFixedPoint toyOp t → subset (lfp toyOp) t := fixedpoint_complete toyOp

end DomainTypedLispFormalization
