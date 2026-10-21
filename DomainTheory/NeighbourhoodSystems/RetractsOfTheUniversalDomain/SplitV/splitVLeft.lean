/-ai
splitVLeft n is the code of the left half, the level set one level above the minimal level whose mask is two to the power of the splitting bit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **`splitVLeft`**: the code for `Y := levelSet (k+1) (2 ^ ℓ₀)`, `V_no_minimal`'s "left" half. -/
def splitVLeft (n : ℕ) : ℕ := Nat.pair (splitVMinLevel n + 1) (2 ^ splitVBit n)

end DomainTheory.NeighbourhoodSystems
