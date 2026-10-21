/-ai
The canonical code of a list code is the canonical list code when that code is nonzero, and otherwise the singleton list code of the master pair, which presents the master neighbourhood of U. The choice is selection on the zero test of the list code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **The code-level canonicalization**, mirroring `canonList` exactly: `canonListCode c` if
non-empty, else the fallback singleton `[masterPairCode]` (presenting `U.master`). -/
def canonCode (c : ℕ) : ℕ :=
  selectFn (isZero (canonListCode c)) (Nat.pair masterPairCode 0 + 1) (canonListCode c)

end DomainTheory.NeighbourhoodSystems
