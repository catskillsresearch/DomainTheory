/-ai
The code-level minimum of first components folds the rational minimum of the accumulator with the first component of each pair code, with parameter zero and seed the one code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The code-level `listMinFst`: fold `ratMinCode` over `c`'s pair-codes, seeded at `oneCode`. -/
def listMinFstCode (c : ℕ) : ℕ :=
  foldCode (fun t => ratMinCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.1)) 0 oneCode c

end DomainTheory.NeighbourhoodSystems
