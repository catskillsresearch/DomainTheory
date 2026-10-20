/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Example12
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23.Basic


namespace DomainTheory.Neighborhood.Example23

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB












/-- **`parityMap`'s relation on a cone, read off.** `cone σ f Y ↔ Y ∈ valElt(scan σ)` — the
defining existential collapses since a cone has a *unique* generating prefix (`cone_injective`).
(Used throughout Exercise 2.16's uniqueness argument.) -/
theorem parityMap_rel_cone (σ : Str) (Y : Set Example12.Token) :
    parityMap.rel (cone σ) Y ↔ (valElt (scan σ)).mem Y := by
  constructor
  · rintro ⟨ρ, hρ, hval⟩
    rw [cone_injective hρ]
    exact hval
  · intro hval
    exact ⟨σ, rfl, hval⟩

end DomainTheory.Neighborhood.Example23
