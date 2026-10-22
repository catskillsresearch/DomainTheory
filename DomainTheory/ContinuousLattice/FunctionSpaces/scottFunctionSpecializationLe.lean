module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottFunctionSubbasis_isOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.specializationLe_generateOpen

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


theorem scottFunctionSpecializationLe {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    SpecializationLe f g ↔ ∀ x, SpecializationLe (f x) (g x) := by
  let : TopologicalSpace (C(X, Y)) := scottFunctionTopology X Y
  constructor
  · intro hfg x U hU hfU
    exact hfg {h | h x ∈ U} (scottFunctionSubbasis_isOpen (X := X) (Y := Y) hU) hfU
  · intro hfg U hU hfU
    exact specializationLe_generateOpen f g hfg hU hfU

end DomainTheory.ContinuousLattice
