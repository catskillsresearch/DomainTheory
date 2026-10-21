/-ai
Every set in the enumeration of U is a neighbourhood of U.

Rewrite the enumerated set as the intervals presented by a canonical list, which form a neighbourhood of U.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_mem_presentedIntervals_canonList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Every `UX n` is a genuine `U`-neighbourhood. -/
theorem U_mem_UX (n : ℕ) : U.mem (UX n) := by
  rw [UX_eq]; exact U_mem_presentedIntervals_canonList _

end DomainTheory.NeighbourhoodSystems
