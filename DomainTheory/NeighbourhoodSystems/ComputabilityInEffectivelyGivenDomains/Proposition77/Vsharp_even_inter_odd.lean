/-ai
The intersection of the enumerated set at 2a+2 with the enumerated set at 2b+1 is empty.

Commute the intersection and apply the law for the intersection of an odd index with an even index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd_inter_even

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_even_inter_odd (a b : ℕ) :
    Vsharp D P (2 * a + 2) ∩ Vsharp D P (2 * b + 1) = ∅ := by
  rw [Set.inter_comm]; exact Vsharp_odd_inter_even P b a

end Proposition77

end DomainTheory.NeighbourhoodSystems
