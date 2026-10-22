module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


section Proposition310

open Finset

namespace IsContinuousLatticeProjection

/-- **Scott 1972, Proposition 3.10(ii).** The inclusion map of a projection is injective. -/
theorem incl_injective (P : IsContinuousLatticeProjection D D') {x y : D} (h : P.incl x = P.incl y) : x = y := by
  rw [← P.retr_incl x, ← P.retr_incl y, h]

end IsContinuousLatticeProjection
end Proposition310
end DomainTheory.ContinuousLattice
