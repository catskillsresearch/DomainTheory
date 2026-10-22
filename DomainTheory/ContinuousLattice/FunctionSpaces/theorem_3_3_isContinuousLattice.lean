/-ai
If D and D' are continuous lattices, then the pointwise-ordered space of Scott maps from D to D' is a continuous lattice. Each Scott map is the supremum of the step maps way below it.

Elements way below a map lie below it. If a map g lies above every element way below f, compare them pointwise. At each argument, the value of f is the supremum of those e' for which some e way below the argument has e' way below f at e. Each corresponding step map is way below f, hence lies below g, and its value at the argument is e'.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_apply_of_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_pointwise_sSup

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- **Scott 1972, Theorem 3.3 (order content).** If `D` and `D'` are continuous lattices, then so
is `[D → D']` under the pointwise order. Every `f` is the supremum of the step functions way below
it: `f = ⊔ {ē[e,e'] | e' ≪ f e}`, and each such step function is way below `f`. -/
theorem theorem_3_3_isContinuousLattice (hD : ContinuousLattice D)
    (hD' : ContinuousLattice D') : ContinuousLattice (ScottMap D D') := by
  constructor
  intro f
  refine ⟨fun h hh => hh.le, fun g hg => ?_⟩
  rw [ScottMap.le_def]
  intro x
  rw [← stepMap_pointwise_sSup hD hD' f x]
  refine sSup_le ?_
  rintro e' ⟨e, hex, he'⟩
  have hle : stepMap e e' ≤ g := hg (stepMap_wayBelow he')
  have hx := (ScottMap.le_def.1 hle) x
  rwa [stepMap_apply_of_wayBelow hex] at hx

end DomainTheory.ContinuousLattice
