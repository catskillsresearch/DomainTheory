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








theorem basicNhhd_inter (n m : ℕ) :
    basicNhhd n ∩ basicNhhd m = basicNhhd (n ||| m) := by
  ext x
  simp [basicNhhd, e_or, Set.union_subset_iff]

end DomainTheory.DataTypesAsLattices
