module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}

namespace memOpen

theorem eq_basicNhhd (k : ℕ) : memOpen k = basicNhhd (2 ^ k) := by
  ext x
  simp [memOpen, basicNhhd, e_pow2, Set.singleton_subset_iff]

end memOpen

end DomainTheory.DataTypesAsLattices
