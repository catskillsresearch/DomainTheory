/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example24
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Exercise218.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise218

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB ApproximableMap














/-- The elementwise value of `kMap` on the finite element `↑(σΣ*)` is `↑((kOut σ)Σ*)`. -/
theorem toElementMap_kMap_cone (σ : Str) :
    kMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (kOut σ)) := by
  apply Element.ext
  intro Y
  rw [← kMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

end DomainTheory.Neighborhood.Exercise218
