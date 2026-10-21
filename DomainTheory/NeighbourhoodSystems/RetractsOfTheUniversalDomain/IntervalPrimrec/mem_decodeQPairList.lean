/-ai
A rational pair lies in a decoded list if and only if it is the decoding of some entry of the decoded code.

Unfold the decoding, rewrite by membership in a mapped list, and commute the equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive








theorem mem_decodeQPairList (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList c ↔ ∃ e ∈ decodeList c, p = decodeRatPair e := by
  unfold decodeQPairList; rw [List.mem_map]; simp [eq_comm]

end DomainTheory.NeighbourhoodSystems
