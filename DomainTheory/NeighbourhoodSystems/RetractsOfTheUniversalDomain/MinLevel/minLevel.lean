/-ai
The minimal level of a level and a mask is the recursion, on the bound one more than the level, that starts at zero and at stage i keeps the value already found when that value is strictly smaller than i, and otherwise returns i when the periodicity test succeeds and i + 1 when it fails. It is the least level, at most the given level, at which the level set is presentable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.isPeriodicMask

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **`minLevel k m`**: the smallest `j ≤ k` such that `levelSet k m` is presentable at level `j`
(`minLevel_isPeriodicMask`, `minLevel_le`); the presentation-independent canonical level of the set
`levelSet k m` (`minLevel_unique`). -/
def minLevel (k m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (isPeriodicMask k i m) i (i + 1)) ih) (k + 1)

end DomainTheory.NeighbourhoodSystems
