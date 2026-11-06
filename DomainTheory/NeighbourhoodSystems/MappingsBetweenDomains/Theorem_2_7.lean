module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace ApproximableMap

/-- Scott's Theorem 2.7: every order isomorphism of domains arises from an approximable map,
and finite (principal) elements are sent to finite elements. -/
theorem theorem_2_7 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (e : V₀.Element ≃o V₁.Element),
      ∃ f : ApproximableMap V₀ V₁, ∀ x, f.toElementMap x = e x) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X),
      ∃ (Y : Set β) (hY : V₁.mem Y), e (V₀.principal hX) = V₁.principal hY) :=
  ⟨@exists_approximable_of_iso, @exists_principal_eq_apply_principal⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
