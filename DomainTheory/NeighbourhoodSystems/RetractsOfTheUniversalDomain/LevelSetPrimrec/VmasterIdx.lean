module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- A fixed index of `V.master = Set.univ`. -/
def VmasterIdx : ℕ := Nat.pair 0 1

end DomainTheory.NeighbourhoodSystems
