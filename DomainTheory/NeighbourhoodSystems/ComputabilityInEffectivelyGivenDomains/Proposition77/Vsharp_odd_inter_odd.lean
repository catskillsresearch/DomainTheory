module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_odd_inter_odd (a b : ℕ) :
    Vsharp D P (2 * a + 1) ∩ Vsharp D P (2 * b + 1) = embZero (P.X a ∩ P.X b) := by
  rw [Vsharp_odd, Vsharp_odd, embZero_inter]

end Proposition77

end DomainTheory.NeighbourhoodSystems
