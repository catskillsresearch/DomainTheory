module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVMinLevel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV.splitVMinMask

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The upsampled mask `M := myUpsample k (k+1) m` for `(k, m) := (splitVMinLevel n, splitVMinMask
n)` — Scott's `M` from `V_no_minimal`, at the code level, fed the *minimal* presentation. -/
def splitVUpsampled (n : ℕ) : ℕ :=
  myUpsample (splitVMinLevel n) (splitVMinLevel n + 1) (splitVMinMask n)

end DomainTheory.NeighbourhoodSystems
