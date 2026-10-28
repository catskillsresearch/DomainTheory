module
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_eq_of_ext
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend
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

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem scottSubspaceExtend_eq_of_ext {e : X → Y} {f g' : X → D} (h : ∀ x, f x = g' x) (y : Y) :
    scottSubspaceExtend e f y = scottSubspaceExtend e g' y := by
  unfold scottSubspaceExtend
  congr 1
  ext d
  simp [Set.mem_ofPred_eq, scottSubspaceExtendInf_eq_of_ext h]

end SubspaceExtension
end DomainTheory.ContinuousLattice
