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
import DomainTheory.ContinuousLattice.FunctionSpaces.retr_wayBelow_of_wayBelow_incl
import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_image_retr_wayBelow


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']







































/-- **Scott 1972, Proposition 2.10(a).** A (Scott-continuous) retract of a continuous lattice is a
continuous lattice. For `d ∈ D` we have, in the ambient `D'`, `i(d) = ⊔{x' | x' ≪ i(d)}`; applying
the retraction `j` (which preserves this directed supremum) gives `d = ⊔{j(x') | x' ≪ i(d)}` in
`D`, and each `j(x') ≪ d` by `retr_wayBelow_of_wayBelow_incl`. Hence any upper bound of
`{x | x ≪ d}` dominates `d`, so `d = ⊔{x | x ≪ d}`. -/
theorem proposition_2_10_a (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') : IsContinuousLattice D := by
  intro d
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  rw [← R.sSup_image_retr_wayBelow hD' d]
  exact sSup_le fun _ ⟨x', hx', hxeq⟩ => hxeq ▸ hb (R.retr_wayBelow_of_wayBelow_incl hx')

end DomainTheory.ContinuousLattice
