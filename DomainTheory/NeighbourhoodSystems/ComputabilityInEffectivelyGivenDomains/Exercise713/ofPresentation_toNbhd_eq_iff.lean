/-ai
For the inclusion structure of a computable presentation, the hint neighbourhoods of two indices coincide if and only if the underlying enumerated neighbourhoods coincide.

Equality of the hint neighbourhoods is mutual inclusion, and each inclusion of hint neighbourhoods is the corresponding inclusion of enumerated neighbourhoods. Mutual inclusion is equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation_INCL
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_ofPresentation_toNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {V : NeighborhoodSystem α}

/-- For `S = ofPresentation P`, two hint neighbourhoods coincide iff the underlying neighbourhoods
do: `Sₙ = Sₘ ↔ Xₙ = Xₘ`. -/
theorem ofPresentation_toNbhd_eq_iff (P : ComputablePresentation V) (n m : ℕ) :
    (ofPresentation P).toNbhd n = (ofPresentation P).toNbhd m ↔ P.X n = P.X m := by
  rw [Set.Subset.antisymm_iff, (ofPresentation P).toNbhd_subset_iff,
    (ofPresentation P).toNbhd_subset_iff]
  show (P.X n ⊆ P.X m ∧ P.X m ⊆ P.X n) ↔ P.X n = P.X m
  exact (Set.Subset.antisymm_iff).symm

end DomainTheory.NeighbourhoodSystems.Exercise713
