/-ai
The master pair code is the pairing of the code of zero with the code of one, a fixed code for the rational pair that presents the master neighbourhood of U.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- A fixed code for the rational pair `(0,1)`, presenting `U.master`. -/
def masterPairCode : ℕ := Nat.pair zeroCode oneCode

end DomainTheory.NeighbourhoodSystems
