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
import DomainTheory.DataTypesAsLattices.Embedding.embed_injective
import DomainTheory.DataTypesAsLattices.Embedding.embed_continuous


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function



theorem theorem_1_6_injective_continuous {X : Type*} [TopologicalSpace X]
    [T0Space X] (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Injective (embed U) ∧ Continuous (embed U) :=
  ⟨embed_injective U hbasis, embed_continuous U hbasis⟩

end DomainTheory.DataTypesAsLattices
