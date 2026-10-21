/-ai
The subbasic open of elements containing k equals the basic neighbourhood of the code 2^k.

Extensionality, using that the finite set coded by 2^k is the singleton of k, turns membership of k into inclusion of that finite set.
ai-/
module

public import Mathlib.Topology.Bases
import all Mathlib.Topology.Bases
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








theorem memOpen_eq_basicNhhd (k : ℕ) : memOpen k = basicNhhd (2 ^ k) := by
  ext x
  simp [memOpen, basicNhhd, e_pow2, Set.singleton_subset_iff]

end DomainTheory.DataTypesAsLattices
