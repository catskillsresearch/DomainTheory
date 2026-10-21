/-ai
The left inverse sends the principal cone of a finite string to the principal cone of the inverse output of that string.

Two elements are equal when they contain the same neighbourhoods. Membership in the image is the inverse relation on the cone, which supplies a prefix equal to the string and an inclusion of the inverse cone, and that inclusion is membership in the principal cone of the inverse output. The converse uses the string itself as the witness prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


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

end DomainTheory.NeighbourhoodSystems.Exercise218
