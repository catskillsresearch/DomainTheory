module

public import DomainTheory.DataTypesAsLattices.Pomega.Pomega
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

def bitList (j : ℕ) : List ℕ :=
  (List.range (j + 1)).filter (fun k => j.testBit k)

class Extensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop where
  out : ∀ n m, val n = val m → val (p n) = val (p m)

end DomainTheory.DataTypesAsLattices
