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


































/-- `lambda` preserves directed suprema: both sides evaluate, pointwise at `(x, y)`, to
`⊔ {f (x, y) | f ∈ 𝓕}`, since suprema in every function lattice involved are pointwise. -/
theorem proposition_3_5_preservesDirectedSup :
    PreservesDirectedSup
      (scottLambda : ScottMap (D × D') D'' → ScottMap D (ScottMap D' D'')) := by
  intro 𝓕 h𝓕 h𝓕dir
  apply ScottMap.ext
  intro x
  apply ScottMap.ext
  intro y
  rw [scottLambda_apply, ScottMap.sSup_apply, ScottMap.sSup_apply, ScottMap.sSup_apply,
    Set.image_image, Set.image_image]
  congr 1

end DomainTheory.ContinuousLattice
