module

public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.SetLike

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}

namespace memOpen

theorem eq_basicNhhd (k : ℕ) : memOpen k = basicNhhd (2 ^ k) := by
  ext x
  simp [memOpen, basicNhhd, e.pow2, Set.singleton_subset_iff]

end memOpen

end DomainTheory.DataTypesAsLattices
