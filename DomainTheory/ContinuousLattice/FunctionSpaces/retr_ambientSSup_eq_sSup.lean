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





































namespace IsContinuousLatticeRetraction


/-- **Scott 1972, Prop 2.10 / March 1972 correction (p. 135).** For directed `S ⊆ D`,
`j(⊔S′) = ⊔S`: the retraction sends the ambient join back to the subspace join. -/
theorem retr_ambientSSup_eq_sSup (R : IsContinuousLatticeRetraction D D') (S : Set D)
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    R.retr (ambientSSup R S) = sSup S := by
  unfold ambientSSup
  have hdir' : DirectedOn (· ≤ ·) (Set.image (R.incl : D → D') S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨R.incl c, Set.mem_image_of_mem _ hc, R.incl.monotone hac, R.incl.monotone hbc⟩
  have hne' : (Set.image (R.incl : D → D') S).Nonempty := Set.image_nonempty.2 hS
  rw [R.retr.preservesDirectedSup_coe (Set.image (R.incl : D → D') S) hne' hdir']
  rw [Set.image_image, Set.image_congr fun a _ => R.retr_incl a]
  simp

end IsContinuousLatticeRetraction
end DomainTheory.ContinuousLattice
