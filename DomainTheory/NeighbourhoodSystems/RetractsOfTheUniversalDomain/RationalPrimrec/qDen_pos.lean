module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive













theorem qDen_pos (c : ℕ) : 0 < qDen c := Nat.succ_pos _

end DomainTheory.NeighbourhoodSystems
