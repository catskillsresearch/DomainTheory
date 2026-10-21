/-ai
Every point of the intervals presented by a list lies strictly below the maximum second component of the list.

A presented point lies strictly below the second component of some pair of the list, and that second component is at most the maximum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_ge

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`listMaxSnd L` strictly upper-bounds `presentedIntervals L`.** -/
theorem listMaxSnd_upper_bound {L : List (ℚ × ℚ)} {x : ℚ} (hx : x ∈ presentedIntervals L) :
    x < listMaxSnd L := by
  obtain ⟨p, hp, -, hx2⟩ := mem_presentedIntervals.mp hx
  exact hx2.trans_le (listMaxSnd_ge hp)

end DomainTheory.NeighbourhoodSystems
