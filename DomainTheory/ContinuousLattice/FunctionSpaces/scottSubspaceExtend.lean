module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]

noncomputable def scottSubspaceExtend (e : X → Y) (f : X → D) (y : Y) : D :=
  sSup { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e f U }

end SubspaceExtension

end DomainTheory.ContinuousLattice
