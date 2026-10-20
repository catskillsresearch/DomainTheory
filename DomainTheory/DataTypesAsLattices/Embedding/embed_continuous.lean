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



theorem embed_continuous {X : Type*} [TopologicalSpace X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    Continuous (embed U) :=
  continuous_generateFrom_iff.2 fun t ⟨n, hn⟩ => by
    subst hn
    change IsOpen (U n)
    exact hbasis.isOpen ⟨n, rfl⟩

end DomainTheory.DataTypesAsLattices
