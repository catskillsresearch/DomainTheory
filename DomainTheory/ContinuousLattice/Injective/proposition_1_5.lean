/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import DomainTheory.ContinuousLattice.Injective.Basic
import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power



open Topology TopologicalSpace

universe u v w


/-- **Scott 1972, Proposition 1.5.** Every `T₀`-space embeds into a power of 𝕆, and that
power is injective. -/
theorem proposition_1_5 (X : Type u) [TopologicalSpace X] [T0Space X] :
    IsInjectiveSpace.{u,u} (Opens X → Prop) ∧
      IsEmbedding (productOfMemOpens X) := by
  refine ⟨?_, productOfMemOpens_isEmbedding X⟩
  exact isInjectiveSpace_sierpinski_power (Opens X)

