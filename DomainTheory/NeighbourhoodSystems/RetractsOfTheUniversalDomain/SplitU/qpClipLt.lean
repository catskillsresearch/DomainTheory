module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip a pair down to `(-∞, m)`: leave the left endpoint, clamp the right endpoint at `m`. -/
def qpClipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)

end DomainTheory.NeighbourhoodSystems
