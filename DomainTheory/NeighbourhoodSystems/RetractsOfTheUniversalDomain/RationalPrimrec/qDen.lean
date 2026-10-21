/-ai
The denominator of a rational code is one more than the second component of the code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The denominator (`d + 1`, always positive) of a rational code. -/
def qDen (c : ℕ) : ℕ := c.unpair.2 + 1

end DomainTheory.NeighbourhoodSystems
