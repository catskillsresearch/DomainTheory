/-ai
The spacing map sends the principal cone of a finite string to the principal cone of the doubling of that string.

Two elements are equal when they contain the same neighbourhoods. Membership in the image is the spacing relation on the cone, which supplies a prefix equal to the string and an inclusion of the doubled cone, and that inclusion is membership in the principal cone of the doubling. The converse uses the string itself as the witness prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap














/-- The elementwise value of `hMap` on the finite element `↑(σΣ*)` is `↑((hOut σ)Σ*)`. -/
theorem toElementMap_hMap_cone (σ : Str) :
    hMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (hOut σ)) := by
  apply Element.ext
  intro Y
  rw [← hMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
