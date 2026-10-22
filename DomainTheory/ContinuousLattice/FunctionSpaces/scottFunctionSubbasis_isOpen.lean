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


theorem scottFunctionSubbasis_isOpen {x : X} {U : Set Y} (hU : IsOpen U) :
    @IsOpen (C(X, Y)) (scottFunctionTopology X Y) {f : C(X, Y) | f x ∈ U} :=
  isOpen_generateFrom_of_mem (s := {f : C(X, Y) | f x ∈ U}) ⟨x, U, hU, rfl⟩

end DomainTheory.ContinuousLattice
