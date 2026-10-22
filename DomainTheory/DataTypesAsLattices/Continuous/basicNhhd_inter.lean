/-ai
The intersection of the basic neighbourhoods of n and of m equals the basic neighbourhood of the bitwise or of n and m.

Extensionality, after unfolding the basic neighbourhood and the identity for the finite set coded by a bitwise or, converts the two inclusions into containment of the union of those finite sets.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
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
