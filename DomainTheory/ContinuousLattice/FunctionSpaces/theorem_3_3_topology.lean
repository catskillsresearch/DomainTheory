/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_wayBelow
import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_isContinuousLattice
import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_finset_sup
import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_isOpen
import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_scottOpen
import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_le_finset_sup_step


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
























/-- **Scott 1972, Theorem 3.3(b).** The Scott (lattice) topology on `[D → D']` agrees with the
topology of pointwise convergence. -/
theorem theorem_3_3_topology (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' := by
  have hL : IsContinuousLattice (ScottMap D D') := theorem_3_3_isContinuousLattice hD hD'
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
