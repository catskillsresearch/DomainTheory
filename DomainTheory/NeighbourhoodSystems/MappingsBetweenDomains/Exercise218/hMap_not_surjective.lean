/-ai
The element map of the spacing map is not surjective.

Assume a preimage of the principal cone of the string false followed by true. The composite of the left inverse with the spacing map is the identity, so that preimage is the left inverse of this cone. Substituting the cone formulas for both maps identifies two principal cones. Principal injectivity and cone injectivity turn that identification into an equality of strings, which simplifies to a contradiction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.toElementMap_hMap_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.toElementMap_kMap_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kMap_comp_hMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap















/-- **Exercise 2.18 — `h` is not an isomorphism.** It is not surjective: `↑(01Σ*)` is not in the
range (any preimage `x` satisfies `x = k(h(x))`, forcing `h(x) = ↑(00Σ*) ≠ ↑(01Σ*)`). -/
theorem hMap_not_surjective : ¬ Function.Surjective hMap.toElementMap := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (B.principal (memB_cone [false, true]))
  have hkhx : kMap.toElementMap (hMap.toElementMap x) = x := by
    rw [← toElementMap_comp, kMap_comp_hMap, toElementMap_idMap]
  rw [hx, toElementMap_kMap_cone] at hkhx
  rw [← hkhx, toElementMap_hMap_cone] at hx
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) hx)
  simp at hcone

end DomainTheory.NeighbourhoodSystems.Exercise218
