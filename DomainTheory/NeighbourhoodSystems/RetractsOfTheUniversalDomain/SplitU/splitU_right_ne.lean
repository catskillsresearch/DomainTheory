module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.qpClipLt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.qpClipGe
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipLtCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipGeCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipLtListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipGeListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.firstElemCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitMidCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitULeft
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitURight
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.UX_splitULeft
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_disjoint

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- **Theorem 8.8(b) Part 4, properness (right)**: `splitURight n` is a *proper* subset of `Xₙ`. -/
theorem splitU_right_ne (n : ℕ) : UX (splitURight n) ≠ UX n := by
  intro hEq
  have hYsub : UX (splitULeft n) ⊆ UX (splitURight n) := by
    rw [hEq, UX_splitULeft]; exact Set.inter_subset_left
  have hYempty : UX (splitULeft n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter subset_rfl hYsub
  exact (U_mem_UX (splitULeft n)).2.1.ne_empty (Set.subset_empty_iff.mp hYempty)

end DomainTheory.NeighbourhoodSystems
