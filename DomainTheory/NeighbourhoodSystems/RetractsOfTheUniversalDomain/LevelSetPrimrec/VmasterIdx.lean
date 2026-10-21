/-ai
The master index of V is the code of the pair of zero and one, a fixed index of the
master neighbourhood, which is the universe.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- A fixed index of `V.master = Set.univ`. -/
def VmasterIdx : ℕ := Nat.pair 0 1

end DomainTheory.NeighbourhoodSystems
