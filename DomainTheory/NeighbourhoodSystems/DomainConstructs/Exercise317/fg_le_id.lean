/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example23
public import DomainTheory.Neighborhood.Exercise316
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise317.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise317

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB ApproximableMap




















/-- **Exercise 3.17 — `f` is a section of `g`.** `f ∘ g ⊑ I_{T^∞}`. -/
theorem fg_le_id : f.comp g ≤ idMap (iterSys T) := by
  intro W Z
  rw [comp_rel, idMap_rel]
  rintro ⟨X, ⟨hW, τ, hX, hWτ⟩, σ, hXσ, hZmem, hσZ⟩
  obtain rfl : τ = σ := cone_injective (hX.symm.trans hXσ)
  exact ⟨hW, hZmem, hWτ.trans hσZ⟩

end DomainTheory.Neighborhood.Exercise317
