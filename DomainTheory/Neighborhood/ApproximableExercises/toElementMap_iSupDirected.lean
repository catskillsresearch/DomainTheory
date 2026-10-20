/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import Mathlib.Data.Set.Image
import DomainTheory.Neighborhood.ApproximableExercises.Basic
import DomainTheory.Neighborhood.ApproximableExercises.mem_iSupDirected


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}







/-- **Exercise 2.11 (Scott 1981, PRG-19).** Approximable mappings *preserve directed unions*:
`f(⋃ᵢ a i) = ⋃ᵢ f(a i)`. Both sides have member `Y` iff `∃ i X, X ∈ a i ∧ X f Y`. -/
theorem toElementMap_iSupDirected (f : ApproximableMap V₀ V₁) {I : Type*} [Nonempty I]
    (a : I → V₀.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) :
    f.toElementMap (NeighborhoodSystem.iSupDirected a hdir) =
      NeighborhoodSystem.iSupDirected (fun i => f.toElementMap (a i))
        (fun i j => by
          obtain ⟨k, hik, hjk⟩ := hdir i j
          exact ⟨k, f.toElementMap_mono hik, f.toElementMap_mono hjk⟩) := by
  apply Element.ext
  intro Y
  rw [mem_toElementMap, NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨i, hi⟩ := (NeighborhoodSystem.mem_iSupDirected a hdir).mp hX
    exact ⟨i, X, hi, hrel⟩
  · rintro ⟨i, X, hi, hrel⟩
    exact ⟨X, (NeighborhoodSystem.mem_iSupDirected a hdir).mpr ⟨i, hi⟩, hrel⟩

end ApproximableMap
end DomainTheory.Neighborhood
