/-ai
splitVBit n is the splitting bit: the least set bit of the upsampled mask, searched below two to the power of one more than the minimal level.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.myFirstBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVUpsampled

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The splitting bit `ℓ₀` — the least set bit of the upsampled mask `M`, bounded by `2 ^ (k+1)`. -/
def splitVBit (n : ℕ) : ℕ :=
  myFirstBit (splitVUpsampled n) (2 ^ (splitVMinLevel n + 1))

end DomainTheory.NeighbourhoodSystems
