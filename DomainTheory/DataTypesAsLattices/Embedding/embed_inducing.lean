/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Topology.Bases
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import DomainTheory.DataTypesAsLattices.FixedPoint
import DomainTheory.DataTypesAsLattices.Embedding.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function



theorem embed_inducing {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsInducing (embed U) := by
  refine ⟨?_⟩
  rw [hbasis.eq_generateFrom]
  change generateFrom (Set.range U) =
    (generateFrom (Set.range memOpen)).induced (embed U)
  rw [induced_generateFrom_eq]
  congr 1
  ext V
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨memOpen n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

end DomainTheory.DataTypesAsLattices
