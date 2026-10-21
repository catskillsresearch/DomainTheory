/-ai
The intersection index of two indices is the combined code of their canonical codes. Lookup through the enumeration canonicalizes again, so no further canonicalization is applied here.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The intersection index: `combineCode` on canonicalized codes (`UX` re-canonicalizes on
lookup, so no further canonicalization is needed here). -/
def Uinter (n m : ℕ) : ℕ := combineCode (canonCode n) (canonCode m)

end DomainTheory.NeighbourhoodSystems
