module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The code-level `listMaxSnd`: fold `ratMaxCode` over `c`'s pair-codes, seeded at `zeroCode`. -/
def listMaxSndCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) 0 zeroCode c

end DomainTheory.NeighbourhoodSystems
