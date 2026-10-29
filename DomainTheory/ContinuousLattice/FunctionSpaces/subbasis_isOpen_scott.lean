module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottFunctionTopology

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

namespace scottFunctionTopology

theorem subbasis_isOpen_scott {x : D} {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    letI : TopologicalSpace D := scottTopologicalSpace
    letI : TopologicalSpace D' := scottTopologicalSpace
    @IsOpen (C(D, D')) (scottFunctionTopology D D') {f : C(D, D') | f x ∈ U} := by
  let : TopologicalSpace D := scottTopologicalSpace
  let : TopologicalSpace D' := scottTopologicalSpace
  exact isOpen_generateFrom_of_mem (s := {f : C(D, D') | f x ∈ U}) ⟨x, U, hU, rfl⟩

end scottFunctionTopology

end DomainTheory.ContinuousLattice
