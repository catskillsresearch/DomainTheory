module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **The code-level canonicalization**, mirroring `canonList` exactly: `canonListCode c` if
non-empty, else the fallback singleton `[masterPairCode]` (presenting `U.master`). -/
def canonCode (c : ℕ) : ℕ :=
  selectFn (isZero (canonListCode c)) (Nat.pair masterPairCode 0 + 1) (canonListCode c)

end DomainTheory.NeighbourhoodSystems
