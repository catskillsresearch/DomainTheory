module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_isContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_finset_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_isOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_scottOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_le_finset_sup_step

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- **Scott 1972, Theorem 3.3(b).** The Scott (lattice) topology on `[D → D']` agrees with the
topology of pointwise convergence. -/
theorem theorem_3_3_topology (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' := by
  have hL : ContinuousLattice (ScottMap D D') := theorem_3_3_isContinuousLattice hD hD'
  apply le_antisymm
  · -- pointwise ⊆ Scott: each subbasic set is Scott-open in the lattice
    apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hUopen, rfl⟩
    exact isOpen_iff_scottOpen.mpr (pointwiseSubbasic_scottOpen x (isOpen_iff_scottOpen.mp hUopen))
  · -- Scott ⊆ pointwise: each Scott-open lattice set is pointwise-open, via the `↟φ` basis
    intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open (ScottMap D D') (scottMapPointwiseTopology D D')]
    intro g hgU
    obtain ⟨φ, hφg, hφsub⟩ := exists_wayBelow_subset hL hU hgU
    obtain ⟨F, hF, hφF⟩ := wayBelow_le_finset_sup_step hD hD' hφg
    refine ⟨⋂ p ∈ F, {h : ScottMap D D' | (p.2 : D') ≪ (h : D → D') p.1}, ?_, ?_, ?_⟩
    · intro h hh
      refine hφsub (WayBelow.le_trans hφF (wayBelow_finset_sup fun p hp => ?_))
      exact stepMap_wayBelow (Set.mem_iInter₂.1 hh p hp)
    · exact @isOpen_biInter_finset (ScottMap D D') (D × D') (scottMapPointwiseTopology D D') F _
        (fun p _ => pointwiseSubbasic_isOpen p.1 (isOpen_iff_scottOpen.mpr (scottOpen_wayBelow p.2)))
    · exact Set.mem_iInter₂.2 fun p hp => hF p hp

end DomainTheory.ContinuousLattice
