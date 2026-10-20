module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.isPeriodicMask

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The raw `Nat.rec`-fold underlying `minLevel k m`, exposed at an arbitrary bound `N` so the
inductive argument below can range over all `N`, specializing to `N = k + 1` at the end. -/
def minLevelFold (k m N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (isPeriodicMask k i m) i (i + 1)) ih) N

end DomainTheory.NeighbourhoodSystems
