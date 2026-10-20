module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414




/-- **Exercise 4.21 (Scott 1981, PRG-19).** `≤` solves Scott's fixed-point equation. -/
theorem leRel_isFixed : leOp leRel = leRel := by
  apply Set.Subset.antisymm
  · rintro ⟨n, m⟩ (h | ⟨k, hk, rfl⟩)
    · exact le_of_eq (h : n = m)
    · exact Nat.le_succ_of_le (hk : n ≤ k)
  · rintro ⟨n, m⟩ (h : n ≤ m)
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact Or.inl h'
    · refine Or.inr ⟨m - 1, ?_, ?_⟩
      · change n ≤ m - 1; omega
      · omega

end DomainTheory.NeighbourhoodSystems.Exercise421
