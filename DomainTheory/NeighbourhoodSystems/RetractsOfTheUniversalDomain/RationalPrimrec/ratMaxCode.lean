/-ai
The maximum code selects, according to the comparison code, the second component of its argument or the first.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `ratMaxCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the larger rational. -/
def ratMaxCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.2 t.unpair.1

end DomainTheory.NeighbourhoodSystems
