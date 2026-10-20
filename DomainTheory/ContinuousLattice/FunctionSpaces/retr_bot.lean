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















































section Proposition310

open Finset

namespace IsContinuousLatticeProjection

theorem retr_bot (P : IsContinuousLatticeProjection D D') : (P.retr : D' → D) ⊥ = ⊥ := by
  have hle : (⊥ : D') ≤ P.incl (⊥ : D) := bot_le
  have heq : (P.retr : D' → D) (P.incl (⊥ : D)) = (⊥ : D) := P.retr_incl (d := (⊥ : D))
  exact le_antisymm (le_trans (P.retr.monotone hle) (le_of_eq heq)) bot_le

end IsContinuousLatticeProjection
end Proposition310
end DomainTheory.ContinuousLattice
