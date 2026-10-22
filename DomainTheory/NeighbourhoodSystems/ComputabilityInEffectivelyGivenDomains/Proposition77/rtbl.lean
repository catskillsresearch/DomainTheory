module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The reverse memo table: `rtbl step w` codes `[g(w-1), …, g 0]`. -/
def rtbl (step : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (w + 1) => Nat.pair (step (Nat.pair w (rtbl step w))) (rtbl step w) + 1

end Proposition77

end DomainTheory.NeighbourhoodSystems
