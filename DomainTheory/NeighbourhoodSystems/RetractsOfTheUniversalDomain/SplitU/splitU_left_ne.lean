module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.UX_splitURight
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_disjoint

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- **Theorem 8.8(b) Part 4, properness (left)**: `splitULeft n` is a *proper* subset of `Xₙ`. -/
theorem splitU_left_ne (n : ℕ) : UX (splitULeft n) ≠ UX n := by
  intro hEq
  have hZsub : UX (splitURight n) ⊆ UX (splitULeft n) := by
    rw [hEq, UX_splitURight]; exact Set.inter_subset_left
  have hZempty : UX (splitURight n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter hZsub subset_rfl
  exact (U_mem_UX (splitURight n)).2.1.ne_empty (Set.subset_empty_iff.mp hZempty)

end DomainTheory.NeighbourhoodSystems
