module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.FixedPoints

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- A finite sup of elements way below `g` is way below `g`. -/
theorem wayBelow_finset_sup {ι L : Type*} [CompleteLattice L] {s : Finset ι} {f : ι → L} {g : L}
    (h : ∀ i ∈ s, f i ≪ g) : s.sup f ≪ g :=
  Finset.sup_induction (p := fun a => a ≪ g) (bot_wayBelow g) (fun _ ha _ hb => ha.sup hb) h

end DomainTheory.ContinuousLattice
