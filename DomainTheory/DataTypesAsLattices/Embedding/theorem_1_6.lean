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
import DomainTheory.DataTypesAsLattices.Embedding.embed_inducing
import DomainTheory.DataTypesAsLattices.Embedding.embed_injective


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function



/-- **Scott 1976, Theorem 1.6 (The embedding theorem).**
Every T₀ space with a countable basis embeds in `Pω`. -/
theorem theorem_1_6 {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsEmbedding (embed U) where
  toIsInducing := embed_inducing U hbasis
  injective := embed_injective U hbasis

end DomainTheory.DataTypesAsLattices
