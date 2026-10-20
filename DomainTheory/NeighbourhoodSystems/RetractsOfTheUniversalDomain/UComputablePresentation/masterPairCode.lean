module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- A fixed code for the rational pair `(0,1)`, presenting `U.master`. -/
def masterPairCode : ℕ := Nat.pair zeroCode oneCode

end DomainTheory.NeighbourhoodSystems
