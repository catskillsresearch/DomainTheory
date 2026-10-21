/-ai
The positive numerator part of a rational code is the first component of the first component of the code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The numerator's positive part `a` of a rational code. -/
def qNumP (c : ℕ) : ℕ := c.unpair.1.unpair.1

end DomainTheory.NeighbourhoodSystems
