/-ai
The rank of a code is a stage by which the finite application tree it codes has appeared in the least-fixed-point construction of valC. The rank of zero is one, and the rank of a successor p + 1 is one more than the larger of the ranks of the two unpairing components of p. Each component is strictly smaller than the paired code, so the recursion is well founded.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A stage by which the finite application tree coded by `n` has appeared
in the least-fixed-point construction of `valC`. -/
noncomputable def valRank : ℕ → ℕ
  | 0 => 1
  | p + 1 => max (valRank (unpair p).1) (valRank (unpair p).2) + 1
decreasing_by
  · exact (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)
  · exact (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
      have := pair_unpair p
      omega)

end DomainTheory.DataTypesAsLattices
