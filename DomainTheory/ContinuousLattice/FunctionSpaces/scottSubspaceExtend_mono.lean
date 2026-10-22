module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono

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
theorem scottSubspaceExtend_mono {e : X → Y} {f g₀ : X → D} (hfg : ∀ x, f x ≤ g₀ x) (y : Y) :
    scottSubspaceExtend e f y ≤ scottSubspaceExtend e g₀ y := by
  apply sSup_le
  intro d hd
  obtain ⟨U, hUopen, hyU, rfl⟩ := hd
  have hmem : scottSubspaceExtendInf e g₀ U ∈
      { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e g₀ U } :=
    ⟨U, hUopen, hyU, rfl⟩
  exact le_trans (scottSubspaceExtendInf_mono hfg U) (le_sSup hmem)

end SubspaceExtension
end DomainTheory.ContinuousLattice
