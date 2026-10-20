/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Exercise221.Basic


namespace DomainTheory.Neighborhood.Exercise221

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB

























/-- **Left-to-right bias / "`x` infinite ⟹ `xy = x`".** On a partial input `σ⊥ = ↑(σΣ*)` the
juxtaposition returns `σ⊥` itself, *independently of `y`*. Since an infinite (total) sequence is the
directed union of its finite approximants `σ⊥`, this says `xy = x` for total infinite `x`. -/
theorem juxtapose_cone (σ : Str) (y : C.Element) :
    juxtapose.toElementMap₂ (C.principal (memC_cone σ)) y = C.principal (memC_cone σ) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, ⟨_, hconeX⟩, _, hY, hZ, hd⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, _⟩
    · exact ⟨hZ, hconeX.trans hsub⟩
    · exact absurd hconeX (cone_not_subset_singleton σ ρ)
  · rintro ⟨hZ, hconeσZ⟩
    exact ⟨cone σ, C.master, ⟨memC_cone σ, subset_rfl⟩, y.master_mem, C.master_mem, hZ,
      Or.inl ⟨σ, rfl, hconeσZ⟩⟩

end DomainTheory.Neighborhood.Exercise221
