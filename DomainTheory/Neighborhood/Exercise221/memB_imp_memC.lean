/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Exercise221.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise221

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB














/-- **`𝔹 ⊆ 𝒞`.** Every neighbourhood of `𝔹` is a neighbourhood of `𝒞`. -/
theorem memB_imp_memC {X : Set Str} (hX : B.mem X) : C.mem X := by
  obtain ⟨σ, rfl⟩ := hX; exact memC_cone σ

end DomainTheory.Neighborhood.Exercise221
