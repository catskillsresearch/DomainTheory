module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.interMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open ApproximableMap


/-- Scott's Exercise 2.10 (meet clause): the pointwise intersection of two approximable maps
is again approximable and acts elementwise by intersection of filters. -/
theorem exercise_2_10 :
    ∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f g : ApproximableMap V₀ V₁) (x : V₀.Element) {Z : Set β},
      ((interMap f g).toElementMap x).mem Z ↔
        (f.toElementMap x).mem Z ∧ (g.toElementMap x).mem Z :=
  mem_toElementMap_interMap

