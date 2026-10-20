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
import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpaceu2eof_retract
import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power
import DomainTheory.ContinuousLattice.Injective.proposition_1_5



open Topology TopologicalSpace

universe u v w



/-- **Scott 1972, Corollary 1.6.** Injective spaces are exactly retracts of powers of 𝕆. -/
theorem corollary_1_6 (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔ ∃ (ι : Type u), Nonempty (IsRetractSubspace D (ι → Prop)) := by
  constructor
  · intro hD
    obtain ⟨r, hr⟩ := hD (productOfMemOpens D) (proposition_1_5 D).2 (ContinuousMap.id D)
    refine ⟨Opens D, ⟨⟨productOfMemOpens D, (proposition_1_5 D).2, r, hr⟩⟩⟩
  · rintro ⟨ι, ⟨R⟩⟩
    exact IsInjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power ι) R.section' R.retraction
      R.retraction_section

