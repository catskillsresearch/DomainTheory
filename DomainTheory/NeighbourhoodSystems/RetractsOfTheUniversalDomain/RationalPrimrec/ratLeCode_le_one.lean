/-ai
Every comparison code is at most one.

The comparison code is a zero test, and a zero test is at most one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive















theorem ratLeCode_le_one (t : ℕ) : ratLeCode t ≤ 1 := isZero_le_one _

end DomainTheory.NeighbourhoodSystems
