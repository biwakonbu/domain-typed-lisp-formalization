import DomainTypedLispFormalization.FormulaSemantics
import DomainTypedLispFormalization.CarrierSet

namespace DomainTypedLispFormalization

variable {α : Type u} [DecidableEq α]

structure ClosureOperator (α : Type u) [DecidableEq α] where
  carrier : List α
  carrier_nodup : carrier.Nodup
  derive : FactSet α -> FactSet α
  derive_bounded : ∀ {s x}, derive s x = true -> x ∈ carrier
  derive_monotone : ∀ {s t}, subset s t -> subset (derive s) (derive t)

def step (op : ClosureOperator α) (s : FactSet α) : FactSet α :=
  union s (op.derive s)

def iterate (op : ClosureOperator α) : Nat → FactSet α
  | 0 => empty
  | n + 1 => step op (iterate op n)

def lfp (op : ClosureOperator α) : FactSet α :=
  iterate op op.carrier.length

def IsFixedPoint (op : ClosureOperator α) (s : FactSet α) : Prop :=
  equiv (step op s) s

def IsLeastFixedPoint (op : ClosureOperator α) (s : FactSet α) : Prop :=
  IsFixedPoint op s ∧ ∀ t, IsFixedPoint op t -> subset s t

theorem step_inflationary (op : ClosureOperator α) (s : FactSet α) :
    subset s (step op s) := by
  exact subset_union_left s (op.derive s)

theorem step_bounded (op : ClosureOperator α) {s : FactSet α} :
    boundedBy op.carrier s -> boundedBy op.carrier (step op s) := by
  intro hs
  apply bounded_union hs
  intro x hx
  exact op.derive_bounded hx

theorem iterate_bounded (op : ClosureOperator α) :
    ∀ n, boundedBy op.carrier (iterate op n) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp [iterate, empty] at hx
  | succ n ih =>
      exact step_bounded op ih

theorem fixed_of_iterate_succ_eq (op : ClosureOperator α) {n : Nat} :
    iterate op (n + 1) = iterate op n -> IsFixedPoint op (iterate op n) := by
  intro h
  simpa [IsFixedPoint, iterate, step] using equiv_of_eq h

theorem iterate_succ_eq_of_fixed (op : ClosureOperator α) {n : Nat}
    (h : IsFixedPoint op (iterate op n)) :
    iterate op (n + 1) = iterate op n := by
  exact eq_of_equiv (by simpa [IsFixedPoint, iterate, step] using h)

theorem iterate_stable_from_fixed (op : ClosureOperator α) {n : Nat}
    (h : IsFixedPoint op (iterate op n)) :
    ∀ m, iterate op (n + m) = iterate op n := by
  have hEq : iterate op (n + 1) = iterate op n := iterate_succ_eq_of_fixed op h
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        iterate op (n + (m + 1)) = step op (iterate op (n + m)) := by
          simp [iterate]
        _ = step op (iterate op n) := by rw [ih]
        _ = iterate op n := by simpa [iterate] using hEq

theorem iterate_chain (op : ClosureOperator α) (n : Nat) :
    subset (iterate op n) (iterate op (n + 1)) := by
  simpa [iterate] using step_inflationary op (iterate op n)

theorem fixedpoint_step_monotone (op : ClosureOperator α) :
    ∀ {s t}, subset s t -> subset (step op s) (step op t) := by
  intro s t hsub
  apply union_subset
  · exact subset_trans hsub (subset_union_left t (op.derive t))
  ·
    have hderive : subset (op.derive s) (op.derive t) := op.derive_monotone hsub
    exact subset_trans hderive (subset_union_right t (op.derive t))

theorem iterate_card_monotone (op : ClosureOperator α) (n : Nat) :
    cardOn op.carrier (iterate op n) ≤ cardOn op.carrier (iterate op (n + 1)) := by
  exact cardOn_mono op.carrier (iterate_chain op n)

theorem not_fixed_before_of_not_fixed_lfp (op : ClosureOperator α) {n : Nat}
    (hn : n ≤ op.carrier.length) (hfinal : ¬ IsFixedPoint op (lfp op)) :
    ¬ IsFixedPoint op (iterate op n) := by
  intro hfix
  have hEq : iterate op op.carrier.length = iterate op n := by
    simpa [lfp, Nat.add_sub_of_le hn] using iterate_stable_from_fixed op hfix (op.carrier.length - n)
  have hEqNext : iterate op (op.carrier.length + 1) = iterate op op.carrier.length := by
    calc
      iterate op (op.carrier.length + 1) = step op (iterate op op.carrier.length) := by
        simp [iterate]
      _ = step op (iterate op n) := by rw [hEq]
      _ = iterate op (n + 1) := by simp [iterate]
      _ = iterate op n := iterate_succ_eq_of_fixed op hfix
      _ = iterate op op.carrier.length := by simpa using hEq.symm
  exact hfinal (fixed_of_iterate_succ_eq op hEqNext)

theorem iterate_stabilizes_by_length (op : ClosureOperator α) :
    IsFixedPoint op (lfp op) := by
  classical
  by_cases hnot : IsFixedPoint op (lfp op)
  · exact hnot
  have hcountLower : ∀ n, n ≤ op.carrier.length -> n ≤ cardOn op.carrier (iterate op n) := by
    intro n hn
    induction n with
    | zero =>
        exact Nat.zero_le _
    | succ n ih =>
        have hnle : n ≤ op.carrier.length := Nat.le_trans (Nat.le_succ n) hn
        have ihn : n ≤ cardOn op.carrier (iterate op n) := ih hnle
        have hneq : ¬ equiv (iterate op n) (iterate op (n + 1)) := by
          intro heq
          apply not_fixed_before_of_not_fixed_lfp op hnle hnot
          simpa [IsFixedPoint, iterate, step] using equiv_symm heq
        have hstrict : cardOn op.carrier (iterate op n) < cardOn op.carrier (iterate op (n + 1)) := by
          apply strict_card_increase_of_subset_not_equiv op.carrier_nodup
          · exact iterate_chain op n
          · exact iterate_bounded op (n + 1)
          · exact hneq
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ihn hstrict)
  have hlen : op.carrier.length ≤ cardOn op.carrier (iterate op op.carrier.length) := by
    exact hcountLower op.carrier.length (Nat.le_refl _)
  have hstrictFinal : cardOn op.carrier (iterate op op.carrier.length) <
      cardOn op.carrier (iterate op (op.carrier.length + 1)) := by
    have hneqFinal : ¬ equiv (iterate op op.carrier.length) (iterate op (op.carrier.length + 1)) := by
      intro heq
      exact hnot (by simpa [lfp, IsFixedPoint, iterate, step] using equiv_symm heq)
    apply strict_card_increase_of_subset_not_equiv op.carrier_nodup
    · exact iterate_chain op op.carrier.length
    · exact iterate_bounded op (op.carrier.length + 1)
    · exact hneqFinal
  have htooLarge : op.carrier.length < cardOn op.carrier (iterate op (op.carrier.length + 1)) := by
    exact Nat.lt_of_le_of_lt hlen hstrictFinal
  have hupper : cardOn op.carrier (iterate op (op.carrier.length + 1)) ≤ op.carrier.length := by
    exact cardOn_le_length op.carrier (iterate op (op.carrier.length + 1))
  exfalso
  exact Nat.not_lt_of_ge hupper htooLarge

theorem lfp_is_fixed_point (op : ClosureOperator α) : IsFixedPoint op (lfp op) := by
  exact iterate_stabilizes_by_length op

theorem lfp_least (op : ClosureOperator α) :
    ∀ t, IsFixedPoint op t -> subset (lfp op) t := by
  intro t hfix
  have hderiveSub : subset (op.derive t) t := by
    intro x hx
    have hStep : step op t x = true := by
      exact subset_union_right t (op.derive t) x hx
    exact hfix.1 x hStep
  have hIterSub : ∀ n, subset (iterate op n) t := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simp [iterate, empty] at hx
    | succ n ih =>
        have hDeriveToT : subset (op.derive (iterate op n)) t := by
          have hDeriveToDeriveT : subset (op.derive (iterate op n)) (op.derive t) :=
            op.derive_monotone ih
          exact subset_trans hDeriveToDeriveT hderiveSub
        simpa [iterate, step] using union_subset ih hDeriveToT
  simpa [lfp] using hIterSub op.carrier.length

theorem fixedpoint_sound (op : ClosureOperator α) :
    IsFixedPoint op (lfp op) := by
  exact lfp_is_fixed_point op

theorem fixedpoint_complete (op : ClosureOperator α) :
    ∀ t, IsFixedPoint op t -> subset (lfp op) t := by
  exact lfp_least op

theorem fixedpoint_least_model_exists (op : ClosureOperator α) :
    IsLeastFixedPoint op (lfp op) := by
  exact ⟨fixedpoint_sound op, fixedpoint_complete op⟩

end DomainTypedLispFormalization
