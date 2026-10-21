/-ai
If two indices present the same neighbourhood of U, their right-hand splits present the same set.

Rewrite each split by its set description, replace the common neighbourhood, and use that the decoded midpoint depends only on that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.UX_splitU2Right
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode_congr

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`splitU2Right`'s output set is a well-defined function of `UX k` as a set.** -/
theorem splitU2Right_congr {n n' : ℕ} (h : UX n = UX n') :
    UX (splitU2Right n) = UX (splitU2Right n') := by
  rw [UX_splitU2Right, UX_splitU2Right, h, splitU2MidCode_congr h]

end DomainTheory.NeighbourhoodSystems
