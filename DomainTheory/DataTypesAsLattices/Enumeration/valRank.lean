module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

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
