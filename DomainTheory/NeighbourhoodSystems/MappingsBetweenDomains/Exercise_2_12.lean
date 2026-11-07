module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.iSupMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open ApproximableMap


/-- Scott's Exercise 2.12: a directed family of approximable maps has a directed supremum
whose elementwise action is the pointwise directed union of the actions. -/
theorem exercise_2_12 :
    ∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
      (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
        (∀ X Y, (f j).rel X Y → (f k).rel X Y))
      (x : V₀.Element) {Y : Set β},
      ((iSupMap f hdir).toElementMap x).mem Y ↔ ∃ i, ((f i).toElementMap x).mem Y :=
  mem_toElementMap_iSupMap

