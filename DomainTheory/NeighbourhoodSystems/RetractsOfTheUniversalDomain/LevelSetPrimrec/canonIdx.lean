module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Keep a code `c = pair k m` unchanged when `levelSet k m` is non-empty; otherwise fall back to
the fixed master code `pair 0 1` (`levelSet 0 1 = univ`, `levelSet_zero_one`). -/
def canonIdx (c : ℕ) : ℕ :=
  selectFn (myLevelSetNonempty c.unpair.1 c.unpair.2) c (Nat.pair 0 1)

end DomainTheory.NeighbourhoodSystems
