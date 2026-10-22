module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The reverse list of memo values `[g(w-1), …, g 0]`. -/
def gList (step : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | (w + 1) => gOf step w :: gList step w

end Proposition77

end DomainTheory.NeighbourhoodSystems
