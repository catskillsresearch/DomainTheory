module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip a rational pair to `[0,1)`, moving `r` up to `0` and `s` down to `1` when needed. Mirrors
`Definition87.lean`'s `private def clip`, redefined here (public) since `canonList`/`canonCode` need
both a list-level and a code-level version of it. -/
def qpClip (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ 0, p.2 ⊓ 1)

end DomainTheory.NeighbourhoodSystems
