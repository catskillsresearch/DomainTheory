module
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
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
theorem scottSubspaceExtendInf_mono_retr {e : X → Y} {g : X → D'}
    (P : ContinuousLatticeProjection D D') (U : Set Y) :
    P.retr (scottSubspaceExtend.inf e g U) ≤ scottSubspaceExtend.inf e (fun x => P.retr (g x)) U := by
  apply le_sInf
  intro d hd
  obtain ⟨x, hxU, rfl⟩ := hd
  have hx : x ∈ e ⁻¹' U := Set.mem_preimage.mpr hxU
  exact (P.retr.monotone (sInf_le (Set.mem_image_of_mem g hx))).trans le_rfl

end SubspaceExtension
end DomainTheory.ContinuousLattice
