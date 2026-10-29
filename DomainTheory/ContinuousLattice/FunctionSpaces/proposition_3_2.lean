module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottFunctionTopology

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem proposition_3_2 {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    (SpecializationPreorder f g ↔ ∀ x, SpecializationPreorder (f x) (g x)) :=
  scottFunctionTopology.specializationPreorder

end DomainTheory.ContinuousLattice
