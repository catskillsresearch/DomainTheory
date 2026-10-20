module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_bot
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, (4.13).** `(a ⊕ b) ∘ (a' ⊕ b') = (a ∘ a') ⊕ (b ∘ b')`. -/
theorem eq_4_13 (a b a' b' : Pomega) :
    comp (plusR a b) (plusR a' b') = plusR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [plusR_app a' b' u]
  rcases dcondSet_cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet_of_zero_not_pos h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero,
      dcondSet_of_zero_not_pos h.1 h.2]
    simp only [comp_app]
  · rw [dcondSet_of_pos_not_zero h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one,
      dcondSet_of_pos_not_zero h.1 h.2]
    simp only [comp_app]
  · rw [dcondSet_of_mixed h.1 h.2, plusR_app_top, dcondSet_of_mixed h.1 h.2]
  · rw [dcondSet_of_empty h.1 h.2, plusR_app_bot, dcondSet_of_empty h.1 h.2]

end DomainTheory.DataTypesAsLattices
