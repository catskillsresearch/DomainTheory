/-ai
The master index is the code of the singleton list whose only pair is zero and one, a fixed index of the master neighbourhood of U.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- A fixed index of `U.master = Ico 0 1`. -/
def UmasterIdx : ℕ := encodeQPairList [((0 : ℚ), (1 : ℚ))]

end DomainTheory.NeighbourhoodSystems
