module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Pack the triple `(eqBit, consBit, interIdx)` into one natural. -/
def packT (e c ii : ℕ) : ℕ := Nat.pair e (Nat.pair c ii)

end Proposition77

end DomainTheory.NeighbourhoodSystems
