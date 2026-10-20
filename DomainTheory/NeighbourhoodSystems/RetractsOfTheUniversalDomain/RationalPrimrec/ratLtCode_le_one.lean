module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive
















theorem ratLtCode_le_one (t : ℕ) : ratLtCode t ≤ 1 := by unfold ratLtCode; omega

end DomainTheory.NeighbourhoodSystems
