module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}

namespace basicNhhd

theorem inter (n m : ℕ) :
    basicNhhd n ∩ basicNhhd m = basicNhhd (n ||| m) := by
  ext x
  simp [basicNhhd, e_or, Set.union_subset_iff]

theorem zero : basicNhhd 0 = Set.univ := by
  ext x
  simp [basicNhhd, e_zero]

theorem mono {n m : ℕ} (h : e n ⊆ e m) : basicNhhd m ⊆ basicNhhd n := by
  intro x hx
  exact h.trans hx

end basicNhhd

end DomainTheory.DataTypesAsLattices
