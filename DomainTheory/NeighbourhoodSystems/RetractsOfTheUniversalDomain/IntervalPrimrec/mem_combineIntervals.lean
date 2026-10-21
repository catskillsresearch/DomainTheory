/-ai
A rational pair lies in the combination of two lists if and only if it is the pair of the join of the left endpoints and the meet of the right endpoints of some pair from each list.

Unfold the combination, rewrite by flat-map membership, and simplify membership in the mapped list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive












theorem mem_combineIntervals {L1 L2 : List (ℚ × ℚ)} {p : ℚ × ℚ} :
    p ∈ combineIntervals L1 L2 ↔ ∃ p1 ∈ L1, ∃ p2 ∈ L2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold combineIntervals
  rw [List.mem_flatMap]
  simp only [List.mem_map, eq_comm]

end DomainTheory.NeighbourhoodSystems
