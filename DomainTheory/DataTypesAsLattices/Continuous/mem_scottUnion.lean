/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import DomainTheory.DataTypesAsLattices.Pomega
import DomainTheory.DataTypesAsLattices.Continuous.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace






theorem mem_scottUnion {f : Pomega → Pomega} {x : Pomega} {k : ℕ} :
    k ∈ scottUnion f x ↔ ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by
  constructor
  · intro hk
    obtain ⟨n, hn, hfk⟩ := Set.mem_iUnion.mp hk
    exact ⟨n, hn, hfk⟩
  · intro ⟨n, hn, hk⟩
    exact Set.mem_iUnion.mpr ⟨n, hn, hk⟩

end DomainTheory.DataTypesAsLattices
