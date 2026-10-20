module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_bot
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inl
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inr
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.5 (ii).** Range of `a ⊕ b`. -/
theorem plusR_typed_iff {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed u (plusR a b) ↔
      u = botElem ∨ u = topElem ∨
        (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
          (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b) := by
  constructor
  · intro hu
    have hu' : u =
        dcondSet (funOf u (ofNat 0))
          (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
          (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))) := by
      simpa [typed, plusR_app] using hu
    rcases dcondSet_cases (funOf u (ofNat 0)) with h | h | h | h
    · refine Or.inr (Or.inr (Or.inl ⟨funOf a (funOf u (ofNat 1)), ?_, ?_⟩))
      · exact hu'.trans (dcondSet_of_zero_not_pos h.1 h.2)
      · exact (retract_app ha (funOf u (ofNat 1))).symm
    · refine Or.inr (Or.inr (Or.inr ⟨funOf b (funOf u (ofNat 1)), ?_, ?_⟩))
      · exact hu'.trans (dcondSet_of_pos_not_zero h.1 h.2)
      · exact (retract_app hb (funOf u (ofNat 1))).symm
    · refine Or.inr (Or.inl ?_)
      exact hu'.trans (dcondSet_of_mixed h.1 h.2)
    · refine Or.inl ?_
      exact hu'.trans (dcondSet_of_empty h.1 h.2)
  · intro h
    rcases h with hu | hu | ⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩
    · rw [hu]; exact plusR_typed_bot a b
    · rw [hu]; exact plusR_typed_top a b
    · rw [hx]; exact plusR_typed_inl hxt
    · rw [hy]; exact plusR_typed_inr hyt

end DomainTheory.DataTypesAsLattices
