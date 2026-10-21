/-ai
The hint neighbourhood of k is contained in the intersection of the hint neighbourhoods of n and m if and only if k is included in both n and m.

Containment in an intersection is containment in each factor, and each of those containments is the corresponding inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- `Sₖ ⊆ Sₙ ∩ Sₘ ↔ INCL(k, n) ∧ INCL(k, m)`. -/
theorem toNbhd_subset_inter_iff (k n m : ℕ) :
    I.toNbhd k ⊆ I.toNbhd n ∩ I.toNbhd m ↔ (I.INCL k n ∧ I.INCL k m) := by
  rw [Set.subset_inter_iff, I.toNbhd_subset_iff, I.toNbhd_subset_iff]

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
