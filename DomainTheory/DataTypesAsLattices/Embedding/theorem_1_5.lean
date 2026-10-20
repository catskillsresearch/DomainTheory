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
import DomainTheory.DataTypesAsLattices.Embedding.isOpen_extend_mem


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function


/-- **Scott 1976, Theorem 1.5 (The extension theorem), continuity.** -/
theorem theorem_1_5 {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨k, rfl⟩
  exact isOpen_extend_mem f k

end DomainTheory.DataTypesAsLattices
