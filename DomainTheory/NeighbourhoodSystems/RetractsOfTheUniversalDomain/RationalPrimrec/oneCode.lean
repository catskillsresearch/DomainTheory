/-ai
The code of the rational one is the pair whose first component is the pair of one and zero and whose second component is zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- A fixed code for the rational `1`. -/
def oneCode : ℕ := Nat.pair (Nat.pair 1 0) 0

end DomainTheory.NeighbourhoodSystems
