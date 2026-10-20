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























































namespace Proposition314









/-- Uniqueness: any value that is a fixed point of `f` and below every pre-fixed point equals
`fix f` (the least fixed point is unique). -/
theorem fix_unique {f : ScottMap D D} {a : D} (hfix : (f : D → D) a = a)
    (hleast : ∀ x, (f : D → D) x ≤ x → a ≤ x) : a = fix f :=
  le_antisymm (hleast (fix f) (le_of_eq (fix_eq f))) (fix_le hfix.le)

end Proposition314
end DomainTheory.ContinuousLattice
