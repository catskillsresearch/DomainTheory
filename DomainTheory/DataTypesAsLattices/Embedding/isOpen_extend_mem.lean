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
import DomainTheory.DataTypesAsLattices.Embedding.mem_extend


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


theorem isOpen_extend_mem {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (k : ℕ) :
    IsOpen {y : Y | k ∈ extend (Y := Y) (X := X) f y} := by
  have : {y : Y | k ∈ extend (Y := Y) (X := X) f y} =
      ⋃ U ∈ {U : Set Y | IsOpen U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x}, U := by
    ext y
    constructor
    · intro hy
      obtain ⟨U, hU, hyU, hall⟩ := (mem_extend f).mp hy
      exact Set.mem_iUnion₂.mpr ⟨U, ⟨hU, hall⟩, hyU⟩
    · intro hy
      obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.mp hy
      exact (mem_extend f).mpr ⟨U, hU.1, hyU, hU.2⟩
  rw [this]
  exact isOpen_biUnion fun _ hU => hU.1

end DomainTheory.DataTypesAsLattices
