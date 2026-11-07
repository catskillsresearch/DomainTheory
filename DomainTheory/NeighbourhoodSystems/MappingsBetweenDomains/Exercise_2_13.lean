module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofContinuous

@[expose] public section

open DomainTheory.NeighbourhoodSystems


/-- Scott's Exercise 2.13: elementwise actions of approximable maps are continuous; continuous
maps satisfy the principal-union membership law; and every continuous map arises as the
elementwise action of an approximable map. -/
theorem exercise_2_13 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁), Continuous fun x => f.toElementMap x) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {c : V₀.Element → V₁.Element}, Continuous c →
      ∀ (x : V₀.Element) {Y : Set β},
        (c x).mem Y ↔ ∃ (X : Set α) (hx : x.mem X), (c (V₀.principal (x.sub hx))).mem Y) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (c : V₀.Element → V₁.Element) (hc : Continuous c) (x : V₀.Element),
      (ApproximableMap.ofContinuous c hc).toElementMap x = c x) :=
  ⟨@ApproximableMap.continuous_toElementMap,
    fun {_ _} {_ _} {_} => NeighborhoodSystem.mem_iff_principal_of_continuous,
    @ApproximableMap.toElementMap_ofContinuous⟩

