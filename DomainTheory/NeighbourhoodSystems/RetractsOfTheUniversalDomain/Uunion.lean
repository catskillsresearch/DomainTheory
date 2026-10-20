module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The union index: list-concatenate the two canonicalized presenting lists. `UX` re-canonicalizes
on lookup, so no further canonicalization of the inputs is needed here (mirrors `Udiff`). -/
def Uunion (n m : ℕ) : ℕ := appendListCode (canonCode n) (canonCode m)

end DomainTheory.NeighbourhoodSystems
