module

public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

@[reducible] noncomputable def scottTopologicalSpace : TopologicalSpace D :=
  Topology.scott D (@Set.univ (Set D))

namespace scottTopologicalSpace

/-- The Scott topology of a partial order is `T₀`. -/
theorem t0Space : @T0Space D scottTopologicalSpace := by
  let : TopologicalSpace D := scottTopologicalSpace
  have : IsScott D (@Set.univ (Set D)) := ⟨rfl⟩
  exact inferInstanceAs (T0Space D)

end scottTopologicalSpace

end DomainTheory.ContinuousLattice
