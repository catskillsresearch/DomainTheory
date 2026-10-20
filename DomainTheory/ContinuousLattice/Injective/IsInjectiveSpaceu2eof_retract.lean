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



open Topology TopologicalSpace

universe u v w


/-- **Scott 1972, Proposition 1.4.** Retracts of injective spaces are injective. -/
theorem IsInjectiveSpace.of_retract {D : Type v} {D' : Type v}
    [TopologicalSpace D] [TopologicalSpace D'] (hD : IsInjectiveSpace.{u} D)
    (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    IsInjectiveSpace.{u} D' := by
  intro X Y _ _ e he f
  obtain ⟨g, hg⟩ := hD e he (s.comp f)
  refine ⟨r.comp g, fun x => ?_⟩
  show r (g (e x)) = f x
  rw [hg x]
  exact hrs (f x)

