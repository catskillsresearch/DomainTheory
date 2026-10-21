/-ai
If two indices present the same neighbourhood of U, their left-hand splits present the same set.

Rewrite each split by its set description, replace the common neighbourhood, and use that the decoded midpoint depends only on that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Left
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode_congr

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`splitU2Left`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Left_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Left n) = UX (splitU2Left n') := by
  rw [UX_splitU2Left, UX_splitU2Left, h, splitU2MidCode_congr h]

end DomainTheory.NeighbourhoodSystems
