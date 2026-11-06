module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.phi

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- Scott's Exercise 2.14: the neighbourhood correspondence of an order isomorphism preserves
intersections of consistent neighbourhoods, and the induced approximable map is containment
after that correspondence. -/
theorem example_214 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (e : V₀.Element ≃o V₁.Element) {X X' : Set α}
      (hX : V₀.mem X) (hX' : V₀.mem X') (hXX' : V₀.mem (X ∩ X')),
      phi e hXX' = phi e hX ∩ phi e hX') ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) {Y : Set β},
      (ApproximableMap.ofIso e).rel X Y ↔ V₁.mem Y ∧ phi e hX ⊆ Y) :=
  ⟨@phi_inter, @rel_ofIso_iff⟩

end DomainTheory.NeighbourhoodSystems
