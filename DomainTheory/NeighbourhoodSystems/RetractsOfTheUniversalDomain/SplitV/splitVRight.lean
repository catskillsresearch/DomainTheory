module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.myClearBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVUpsampled
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **`splitVRight`**: the code for `Z := levelSet (k+1) (M ^^^ 2 ^ ℓ₀)`, `V_no_minimal`'s "right"
half — `myClearBit` stands in for `^^^` (justified since `ℓ₀` is, by construction, a genuinely set
bit of `M`; `myClearBit_eq_xor`, `(e)(b)(ii)`). -/
def splitVRight (n : ℕ) : ℕ :=
  Nat.pair (splitVMinLevel n + 1) (myClearBit (splitVUpsampled n) (splitVBit n))

end DomainTheory.NeighbourhoodSystems
