/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.Theorem212
import Mathlib.Order.GaloisConnection.Basic
import DomainTheory.ContinuousLattice.InverseLimits.Basic


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))



















/-- The explicit inverse-limit topology is `T₀`, since the inclusion into the product of the
stage Scott spaces is an embedding. -/
theorem inverseLimit_t0Space :
    @T0Space (InverseLimit D P) (inverseLimitTopology D P) := by
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  let : ∀ n, T0Space (D n) := fun _ => scottTopology_t0Space
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  have hval : Topology.IsEmbedding (Subtype.val : InverseLimit D P → ∀ n, D n) :=
    ⟨⟨rfl⟩, Subtype.val_injective⟩
  exact hval.t0Space

end InverseLimit
end DomainTheory.ContinuousLattice
