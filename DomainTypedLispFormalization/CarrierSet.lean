namespace DomainTypedLispFormalization

abbrev FactSet (α : Type u) := α → Bool

def empty : FactSet α := fun _ => false

def union (s t : FactSet α) : FactSet α := fun x => s x || t x

def subset (s t : FactSet α) : Prop := ∀ x, s x = true → t x = true

def equiv (s t : FactSet α) : Prop := subset s t ∧ subset t s

def boundedBy (carrier : List α) (s : FactSet α) : Prop := ∀ x, s x = true → x ∈ carrier

def cardOn (carrier : List α) (s : FactSet α) : Nat := carrier.countP s

theorem eq_false_of_ne_true {b : Bool} (h : b ≠ true) : b = false := by
  cases b <;> simp at h <;> simp

theorem subset_refl (s : FactSet α) : subset s s := by
  intro x hx
  exact hx

theorem subset_trans {r s t : FactSet α} : subset r s → subset s t → subset r t := by
  intro hrs hst x hx
  exact hst x (hrs x hx)

theorem equiv_refl (s : FactSet α) : equiv s s := by
  exact ⟨subset_refl s, subset_refl s⟩

theorem equiv_symm {s t : FactSet α} : equiv s t → equiv t s := by
  intro h
  exact ⟨h.2, h.1⟩

theorem equiv_trans {r s t : FactSet α} : equiv r s → equiv s t → equiv r t := by
  intro hrs hst
  exact ⟨subset_trans hrs.1 hst.1, subset_trans hst.2 hrs.2⟩

theorem equiv_of_eq {s t : FactSet α} (h : s = t) : equiv s t := by
  cases h
  exact equiv_refl s

theorem eq_of_equiv {s t : FactSet α} (h : equiv s t) : s = t := by
  funext x
  by_cases hs : s x = true
  · have ht : t x = true := h.1 x hs
    simp [hs, ht]
  · have hsFalse : s x = false := eq_false_of_ne_true hs
    have htFalse : t x = false := by
      by_cases ht : t x = true
      · exact False.elim (hs (h.2 x ht))
      · exact eq_false_of_ne_true ht
    simp [hsFalse, htFalse]

theorem subset_union_left (s t : FactSet α) : subset s (union s t) := by
  intro x hx
  simp [union, hx]

theorem subset_union_right (s t : FactSet α) : subset t (union s t) := by
  intro x hx
  simp [union, hx]

theorem union_subset {r s t : FactSet α} : subset r t → subset s t → subset (union r s) t := by
  intro hrt hst x hx
  have hor : r x = true ∨ s x = true := by
    simpa [union] using hx
  cases hor with
  | inl hrx => exact hrt x hrx
  | inr hsx => exact hst x hsx

theorem bounded_union {carrier : List α} {s t : FactSet α} :
    boundedBy carrier s → boundedBy carrier t → boundedBy carrier (union s t) := by
  intro hs ht x hx
  have hor : s x = true ∨ t x = true := by
    simpa [union] using hx
  cases hor with
  | inl hsx => exact hs x hsx
  | inr htx => exact ht x htx

theorem cardOn_cons (a : α) (carrier : List α) (s : FactSet α) :
    cardOn (a :: carrier) s = (if s a then 1 else 0) + cardOn carrier s := by
  simpa [cardOn, Nat.add_comm] using List.countP_cons (p := s) (a := a) (l := carrier)

theorem cardOn_le_length (carrier : List α) (s : FactSet α) :
    cardOn carrier s ≤ carrier.length := by
  simpa [cardOn, List.countP_eq_length_filter] using List.length_filter_le s carrier

theorem cardOn_mono (carrier : List α) {s t : FactSet α} :
    subset s t → cardOn carrier s ≤ cardOn carrier t := by
  induction carrier generalizing s t with
  | nil =>
      intro _hsub
      simp [cardOn]
  | cons a as ih =>
      intro hsub
      have htail : subset s t := by
        intro x hx
        exact hsub x hx
      by_cases hs : s a = true
      · have ht : t a = true := hsub a hs
        simpa [cardOn_cons, hs, ht] using Nat.add_le_add_left (ih htail) 1
      · have hsFalse : s a = false := eq_false_of_ne_true hs
        by_cases ht : t a = true
        · simpa [cardOn_cons, hsFalse, ht, Nat.add_comm] using Nat.le_succ_of_le (ih htail)
        · have htFalse : t a = false := eq_false_of_ne_true ht
          simpa [cardOn_cons, hsFalse, htFalse] using ih htail

theorem count_strict_of_subset_and_witness {carrier : List α} (hnd : carrier.Nodup)
    {s t : FactSet α} (hsub : subset s t) {x : α} (hx : x ∈ carrier)
    (htx : t x = true) (hsx : s x = false) :
    cardOn carrier s < cardOn carrier t := by
  induction carrier generalizing s t x with
  | nil =>
      cases hx
  | cons a as ih =>
      cases hnd with
      | @cons _ _ hnotin htail =>
          have hmem : x = a ∨ x ∈ as := by
            simpa using hx
          cases hmem with
          | inl hxa =>
              subst hxa
              have htailLe : cardOn as s ≤ cardOn as t := cardOn_mono as hsub
              rw [cardOn_cons, cardOn_cons]
              simp [hsx, htx]
              simpa [Nat.add_comm] using Nat.lt_succ_of_le htailLe
          | inr hxTail =>
              have htailStrict : cardOn as s < cardOn as t := ih htail hsub hxTail htx hsx
              rw [cardOn_cons, cardOn_cons]
              have hheadLe : (if s a then 1 else 0) ≤ (if t a then 1 else 0) := by
                by_cases hs : s a = true
                · have ht : t a = true := hsub a hs
                  simp [hs, ht]
                · have hsFalse : s a = false := eq_false_of_ne_true hs
                  by_cases ht : t a = true
                  · simp [hsFalse, ht]
                  · have htFalse : t a = false := eq_false_of_ne_true ht
                    simp [hsFalse, htFalse]
              exact Nat.add_lt_add_of_le_of_lt hheadLe htailStrict

theorem exists_witness_of_not_subset {s t : FactSet α} :
    ¬ subset t s → ∃ x, t x = true ∧ s x = false := by
  classical
  intro hnot
  obtain ⟨x, hx⟩ := Classical.not_forall.mp hnot
  by_cases htx : t x = true
  · have hsNot : ¬ s x = true := by
      intro hs
      exact hx (by intro _; exact hs)
    exact ⟨x, htx, eq_false_of_ne_true hsNot⟩
  · exfalso
    apply hx
    intro h
    exact False.elim (htx h)

theorem strict_card_increase_of_subset_not_equiv {carrier : List α} (hnd : carrier.Nodup)
    {s t : FactSet α} (hsub : subset s t) (htBounded : boundedBy carrier t)
    (hneq : ¬ equiv s t) :
    cardOn carrier s < cardOn carrier t := by
  have hnot : ¬ subset t s := by
    intro hts
    exact hneq ⟨hsub, hts⟩
  obtain ⟨x, htx, hsx⟩ := exists_witness_of_not_subset hnot
  have hx : x ∈ carrier := htBounded x htx
  exact count_strict_of_subset_and_witness hnd hsub hx htx hsx

end DomainTypedLispFormalization
