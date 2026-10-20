/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import DomainTheory.DataTypesAsLattices.FixedPoint

/-!
# Scott 1976, §1 — extension and embedding into `Pω`

Theorems 1.5 and 1.6.
-/

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace Topology Function

/-- **Scott 1976, Theorem 1.5.** Maximal continuous extension of
`f : X → Pω` along a subspace inclusion `X ⊆ Y`:
`f̄(y) = ⋃ { ⋂ {f(x) | x ∈ X ∩ U} | y ∈ U, U open in Y }`. -/
def extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (y : Y) : Pomega :=
  ⋃₀ { t | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ t = ⋂₀ (f '' {x : X | ↑x ∈ U}) }

/-- **Scott 1976, Theorem 1.6.** The embedding `ε(x) = {n | x ∈ U n}`. -/
def embed {X : Type*} (U : ℕ → Set X) (x : X) : Pomega :=
  {n | x ∈ U n}
end DomainTheory.DataTypesAsLattices
