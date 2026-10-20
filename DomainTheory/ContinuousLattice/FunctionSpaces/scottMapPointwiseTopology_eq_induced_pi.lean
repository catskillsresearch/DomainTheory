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
import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_isOpen


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
























/-- Scott's manually generated pointwise topology on `ScottMap` is the subspace topology inherited
from the literal Pi product of the codomain Scott topology. -/
theorem scottMapPointwiseTopology_eq_induced_pi :
    scottMapPointwiseTopology D D' = scottMapInducedPiTopology D D' := by
  apply le_antisymm
  · let : TopologicalSpace D' := scottTopologicalSpace
    let : TopologicalSpace (ScottMap D D') := scottMapPointwiseTopology D D'
    change scottMapPointwiseTopology D D' ≤ scottMapInducedPiTopology D D'
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU => pointwiseSubbasic_isOpen (D := D) (D' := D') x hU
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hU, rfl⟩
    let : TopologicalSpace D' := scottTopologicalSpace
    change @IsOpen (ScottMap D D')
      (TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
        (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace)))
      {f : ScottMap D D' | (f : D → D') x ∈ U}
    rw [isOpen_induced_iff]
    exact ⟨{g : D → D' | g x ∈ U}, (@continuous_apply D (fun _ => D')
      (fun _ => scottTopologicalSpace) x).isOpen_preimage U hU, rfl⟩

end DomainTheory.ContinuousLattice
