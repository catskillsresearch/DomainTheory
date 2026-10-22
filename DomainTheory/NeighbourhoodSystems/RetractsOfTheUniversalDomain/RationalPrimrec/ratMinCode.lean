module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `ratMinCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the smaller rational. -/
def ratMinCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.1 t.unpair.2

end DomainTheory.NeighbourhoodSystems
