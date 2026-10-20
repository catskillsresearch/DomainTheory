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


theorem mem_extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) {y : Y} {k : ℕ} :
    k ∈ extend (Y := Y) (X := X) f y ↔
      ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x := by
  constructor
  · intro hk
    rcases Set.mem_sUnion.mp hk with ⟨t, ⟨U, hU, hy, rfl⟩, hkt⟩
    refine ⟨U, hU, hy, ?_⟩
    intro x hx
    exact Set.mem_sInter.mp hkt (f x) ⟨x, hx, rfl⟩
  · intro ⟨U, hU, hy, hall⟩
    refine Set.mem_sUnion.mpr ⟨⋂₀ (f '' {x : X | ↑x ∈ U}), ⟨U, hU, hy, rfl⟩, ?_⟩
    intro t ht
    rcases ht with ⟨x, hx, rfl⟩
    exact hall x hx

end DomainTheory.DataTypesAsLattices
