/-ai
The negative numerator part of a rational code is the second component of the first component of the code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The numerator's negative part `b` of a rational code (so the numerator is `a - b`). -/
def qNumN (c : ℕ) : ℕ := c.unpair.1.unpair.2

end DomainTheory.NeighbourhoodSystems
