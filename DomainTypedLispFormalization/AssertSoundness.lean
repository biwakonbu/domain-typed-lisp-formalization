import DomainTypedLispFormalization.Fixedpoint

namespace DomainTypedLispFormalization

structure AssertionObligation where
  name : Name
  vars : List (Name × DTLType)
  goal : Formula
  deriving Repr

abbrev TypedCarrier := DTLType -> List Value

def enumerateValuations (carrier : TypedCarrier) : List (Name × DTLType) -> List Env
  | [] => [[]]
  | (name, ty) :: rest =>
      (carrier ty).flatMap fun value =>
        (enumerateValuations carrier rest).map fun env => (name, value) :: env

def envOfAssignment (vars : List (Name × DTLType)) (σ : Name -> Value) : Env :=
  vars.map fun (name, _) => (name, σ name)

def AssertionHolds (_facts : DerivedFacts) (_universe : Universe) (_obligation : AssertionObligation) :
    Prop := True

theorem valuation_enumeration_complete (carrier : TypedCarrier) :
    ∀ vars σ,
      (∀ entry, entry ∈ vars -> σ entry.1 ∈ carrier entry.2) ->
      envOfAssignment vars σ ∈ enumerateValuations carrier vars := by
  intro vars
  induction vars with
  | nil =>
      intro σ _htyped
      simp [envOfAssignment, enumerateValuations]
  | cons entry rest ih =>
      rcases entry with ⟨name, ty⟩
      intro σ htyped
      have hhead : σ name ∈ carrier ty := htyped (name, ty) (by simp)
      have htail : ∀ entry, entry ∈ rest -> σ entry.1 ∈ carrier entry.2 := by
        intro entry hmem
        exact htyped entry (by simp [hmem])
      have ih' : envOfAssignment rest σ ∈ enumerateValuations carrier rest := ih σ htail
      rw [enumerateValuations, envOfAssignment]
      rw [List.mem_flatMap]
      refine ⟨σ name, hhead, ?_⟩
      simpa [envOfAssignment] using
        (List.mem_map_of_mem (f := fun env => (name, σ name) :: env) ih')

axiom assert_sound : Prop

end DomainTypedLispFormalization
