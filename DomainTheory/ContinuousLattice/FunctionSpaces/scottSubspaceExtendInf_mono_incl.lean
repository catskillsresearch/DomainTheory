module
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
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

omit [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y] in
theorem scottSubspaceExtendInf_mono_incl {e : X → Y} {f : X → D} {g : X → D'}
    (P : IsContinuousLatticeProjection D D') (hfg : ∀ x, f x = P.retr (g x)) (U : Set Y) :
    scottSubspaceExtendInf e (fun x => P.incl (f x)) U ≤ scottSubspaceExtendInf e g U := by
  apply le_sInf
  intro d hd
  obtain ⟨x, hxU, rfl⟩ := hd
  have hx : x ∈ e ⁻¹' U := Set.mem_preimage.mpr hxU
  have hmem : P.incl (f x) ∈ (fun x => P.incl (f x)) '' (e ⁻¹' U) :=
    Set.mem_image_of_mem _ hx
  have hincl : P.incl (f x) ≤ g x := by rw [hfg x]; exact P.incl_retr_le (g x)
  exact le_trans (sInf_le hmem) hincl

end SubspaceExtension
end DomainTheory.ContinuousLattice
