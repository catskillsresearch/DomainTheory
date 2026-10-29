module

public import DomainTheory.ContinuousLattice.Specialization.SpecializationPreorder
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottFunctionTopology
public import Mathlib.Data.Set.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem proposition_3_2 {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    (SpecializationPreorder f g ↔ ∀ x, SpecializationPreorder (f x) (g x)) :=
  scottFunctionSpecializationPreorder

end DomainTheory.ContinuousLattice
