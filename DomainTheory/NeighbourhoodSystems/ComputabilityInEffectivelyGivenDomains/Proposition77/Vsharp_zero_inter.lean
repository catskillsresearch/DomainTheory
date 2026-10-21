/-ai
The intersection of the enumerated set at 0 with the enumerated set at m equals the enumerated set at m.

The value at 0 is the master neighbourhood, and the value at m is a section neighbourhood, hence contained in the master neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_zero_inter (m : ℕ) : Vsharp D P 0 ∩ Vsharp D P m = Vsharp D P m := by
  rw [Vsharp_zero, Set.inter_eq_right]; exact memS_subset_gamma (Vsharp_mem P m)

end Proposition77

end DomainTheory.NeighbourhoodSystems
