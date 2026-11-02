module

public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import Mathlib.Order.SetNotation
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.SetLike

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace basicNhhd

theorem eq_iInter (n : ℕ) :
    basicNhhd n = ⋂ k ∈ e n, memOpen k := by
  ext x
  simp [basicNhhd, memOpen, Set.subset_def]

end basicNhhd

end DomainTheory.DataTypesAsLattices
