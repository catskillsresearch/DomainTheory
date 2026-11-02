module

public import DomainTheory.DataTypesAsLattices.Pomega.e
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.SetLike

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}

namespace basicNhhd

theorem inter (n m : ℕ) :
    basicNhhd n ∩ basicNhhd m = basicNhhd (n ||| m) := by
  ext x
  simp [basicNhhd, e.or, Set.union_subset_iff]

theorem zero : basicNhhd 0 = Set.univ := by
  ext x
  simp [basicNhhd, e.zero]

theorem mono {n m : ℕ} (h : e n ⊆ e m) : basicNhhd m ⊆ basicNhhd n := by
  intro x hx
  exact h.trans hx

end basicNhhd

end DomainTheory.DataTypesAsLattices
