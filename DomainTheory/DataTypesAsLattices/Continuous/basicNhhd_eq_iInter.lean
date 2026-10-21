/-ai
The basic neighbourhood of a code n equals the intersection, over every k in the finite set coded by n, of the subbasic opens of elements that contain k.

Extensionality, after unfolding the basic neighbourhood, the subbasic open, and the meaning of subset, makes the two sides the same condition on x.
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


/-- A basic neighbourhood is a finite intersection of subbasic opens. -/
theorem basicNhhd_eq_iInter (n : ℕ) :
    basicNhhd n = ⋂ k ∈ e n, memOpen k := by
  ext x
  simp [basicNhhd, memOpen, Set.subset_def]

end DomainTheory.DataTypesAsLattices
