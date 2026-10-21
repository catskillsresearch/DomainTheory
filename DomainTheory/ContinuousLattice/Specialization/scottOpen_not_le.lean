/-ai
The set of elements that fail to lie below a fixed element L is Scott-open.

If a fails to lie below L and a lies below b, then b fails to lie below L, since otherwise a would lie below L. If the supremum of a set lies in this set, some member does too: if every member lay below L, the supremum would lie below L.
ai-/
module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
import all Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
import all Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
import all Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]


variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]


variable {x : ι → D} {L y : D}

/-- The complement of a principal lower set `Iic L` is Scott-open: it is an upper set, and it
is inaccessible by directed suprema because if every member of a directed `S` lies below `L`
then so does `⊔S`. -/
theorem scottOpen_not_le (L : D) : ScottOpen {z : D | ¬ z ≤ L} := by
  refine ⟨fun a b hab ha hb => ha (le_trans hab hb), fun S hSne hSdir hmem => ?_⟩
  by_contra hcon
  refine hmem (sSup_le fun s hs => ?_)
  by_contra hsL
  exact hcon ⟨s, hs, hsL⟩

end DomainTheory.ContinuousLattice
