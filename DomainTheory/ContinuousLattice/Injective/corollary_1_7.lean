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



/-- **Scott 1972, Corollary 1.7.** A space is injective iff it is a retract of every
super-space of which it is a subspace. -/
theorem corollary_1_7 (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (e : D → Y), IsEmbedding e →
        ∃ r : C(Y, D), ∀ d, r (e d) = d := by
  constructor
  · intro hD Y _ e he
    obtain ⟨r, hr⟩ := hD e he (ContinuousMap.id D)
    exact ⟨r, hr⟩
  · intro hD
    obtain ⟨r, hr⟩ := hD (productOfMemOpens D) (proposition_1_5 D).2
    exact IsInjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power (Opens D))
      (productOfMemOpens D) r hr
