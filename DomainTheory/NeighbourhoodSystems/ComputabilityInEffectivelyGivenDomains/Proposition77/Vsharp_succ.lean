module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- One-step unfolding of `Vsharp` at a successor index. -/
theorem Vsharp_succ (k : ℕ) :
    Vsharp D P (k + 1) =
      if (k + 1) % 2 = 1 then embZero (P.X (k / 2))
      else embPair (Vsharp D P ((k - 1) / 2).unpair.1) (Vsharp D P ((k - 1) / 2).unpair.2) := by
  rw [Vsharp]

end Proposition77

end DomainTheory.NeighbourhoodSystems
