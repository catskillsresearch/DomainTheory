module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.landStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The iterative bitwise AND: iterate `landStep` `a + b` times from the initial state, and read off
the accumulator. -/
def myLand (a b : ℕ) : ℕ :=
  (landStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

end DomainTheory.NeighbourhoodSystems
