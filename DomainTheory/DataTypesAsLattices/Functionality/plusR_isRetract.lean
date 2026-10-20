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















/-- **Scott 1976, Theorem 4.5 (i).** `a ⊕ b` is a retract when `a` and `b` are. -/
theorem plusR_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (plusR a b) := by
  change plusR a b =
    graph (fun u => funOf (plusR a b) (funOf (plusR a b) u))
  apply graph_ext
  intro u
  rw [plusR_app a b u]
  rcases dcondSet_cases (funOf u (ofNat 0)) with h | h | h | h
  · rw [dcondSet_of_zero_not_pos h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero, retract_app ha]
  · rw [dcondSet_of_pos_not_zero h.1 h.2, plusR_app,
      pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one, retract_app hb]
  · rw [dcondSet_of_mixed h.1 h.2, plusR_app_top]
  · rw [dcondSet_of_empty h.1 h.2, plusR_app_bot]

end DomainTheory.DataTypesAsLattices
