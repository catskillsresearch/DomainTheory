module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_pointwise_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_apply_of_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_le_finset_sup_step
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_scottOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_isOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_finset_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseTopology
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseTopology_eq_induced_pi
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapInducedPiTopology

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem theorem_3_3.isContinuousLattice (hD : ContinuousLattice D)
    (hD' : ContinuousLattice D') : ContinuousLattice (ScottMap D D') := by
  refine { out := ?_ }
  intro f
  refine ⟨fun h hh => hh.le, fun g hg => ?_⟩
  rw [ScottMap.le_def]
  intro x
  rw [← stepMap_pointwise_sSup hD hD' f x]
  refine sSup_le ?_
  rintro e' ⟨e, hex, he'⟩
  have hle : stepMap e e' ≤ g := hg (stepMap_wayBelow he')
  have hx := (ScottMap.le_def.1 hle) x
  rwa [stepMap_apply_of_wayBelow hex] at hx

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem theorem_3_3.topology (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' := by
  have hL : ContinuousLattice (ScottMap D D') := theorem_3_3.isContinuousLattice hD hD'
  apply le_antisymm
  ·
    apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hUopen, rfl⟩
    exact ScottOpen.isOpen_iff.mpr (pointwiseSubbasic_scottOpen x (ScottOpen.isOpen_iff.mp hUopen))
  ·
    intro U hU
    rw [ScottOpen.isOpen_iff] at hU
    rw [@isOpen_iff_forall_mem_open (ScottMap D D') (scottMapPointwiseTopology D D')]
    intro g hgU
    obtain ⟨φ, hφg, hφsub⟩ := exists_wayBelow_subset hL hU hgU
    obtain ⟨F, hF, hφF⟩ := wayBelow_le_finset_sup_step hD hD' hφg
    refine ⟨⋂ p ∈ F, {h : ScottMap D D' | (p.2 : D') ≪ (h : D → D') p.1}, ?_, ?_, ?_⟩
    · intro h hh
      refine hφsub (WayBelow.le_trans hφF (wayBelow_finset_sup fun p hp => ?_))
      exact stepMap_wayBelow (Set.mem_iInter₂.1 hh p hp)
    · exact @isOpen_biInter_finset (ScottMap D D') (D × D') (scottMapPointwiseTopology D D') F _
        (fun p _ => pointwiseSubbasic_isOpen p.1 (ScottOpen.isOpen_iff.mpr (scottOpen_wayBelow p.2)))
    · exact Set.mem_iInter₂.2 fun p hp => hF p hp

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem theorem_3_3.topology_induced_pi (hD : ContinuousLattice D)
    (hD' : ContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
      scottMapInducedPiTopology D D' := by
  rw [theorem_3_3.topology hD hD', scottMapPointwiseTopology_eq_induced_pi]

end DomainTheory.ContinuousLattice
