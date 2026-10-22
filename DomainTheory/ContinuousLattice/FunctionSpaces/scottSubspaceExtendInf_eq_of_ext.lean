/-ai
If two maps from X into a complete lattice agree at every point, then their subspace-extension infima on any subset U of Y agree.

The images of the preimage of U under the two maps are the same set, because the maps take the same value at each point of the preimage.
ai-/
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


section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]


omit [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y] in
theorem scottSubspaceExtendInf_eq_of_ext {e : X → Y} {f g' : X → D} (h : ∀ x, f x = g' x) (U : Set Y) :
    scottSubspaceExtendInf e f U = scottSubspaceExtendInf e g' U := by
  unfold scottSubspaceExtendInf
  congr 1
  ext d
  simp [Set.mem_image, Set.mem_preimage, h]

end SubspaceExtension
end DomainTheory.ContinuousLattice
