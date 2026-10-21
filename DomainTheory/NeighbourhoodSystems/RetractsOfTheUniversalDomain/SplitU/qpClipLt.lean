/-ai
qpClipLt m p clips a rational pair down to the open ray below m by leaving the left endpoint and replacing the right endpoint with the minimum of that endpoint and m.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip a pair down to `(-∞, m)`: leave the left endpoint, clamp the right endpoint at `m`. -/
def qpClipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)

end DomainTheory.NeighbourhoodSystems
