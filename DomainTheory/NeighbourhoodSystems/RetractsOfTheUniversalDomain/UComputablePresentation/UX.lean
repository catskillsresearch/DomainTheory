/-ai
The enumeration of U sends an index to the set of intervals presented by the rational-pair list decoded from its canonical code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`𝒰`'s enumeration**: canonicalize the `List (ℚ × ℚ)` coded by `n`. -/
def UX (n : ℕ) : Set ℚ := presentedIntervals (decodeQPairList (canonCode n))

end DomainTheory.NeighbourhoodSystems
