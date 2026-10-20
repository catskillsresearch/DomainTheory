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


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

















































section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]



omit [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y] in
theorem scottSubspaceExtendInf_mono_incl_apply {e : X → Y} {f : X → D} (U : Set Y)
    (P : IsContinuousLatticeProjection D D') :
    P.incl (scottSubspaceExtendInf e f U) ≤ scottSubspaceExtendInf e (fun x => P.incl (f x)) U := by
  apply le_sInf
  intro d hd
  obtain ⟨x, hxU, rfl⟩ := hd
  exact P.incl.monotone (sInf_le (Set.mem_image_of_mem f (Set.mem_preimage.mpr hxU)))

end SubspaceExtension
end DomainTheory.ContinuousLattice
