module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodEquiv

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Proposition 3.2: pairing is monotone and order-reflecting in each factor, and every
    product ideal element is uniquely a pairing of its projections. -/
theorem proposition_3_2 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {x x' : V₀.Element} {y y' : V₁.Element},
      pair x y ≤ pair x' y' ↔ x ≤ x' ∧ y ≤ y') ∧
    (∀ {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β),
      Nonempty ((prod V₀ V₁).Element ≃o V₀.Element × V₁.Element)) :=
  ⟨@pair_le_pair_iff, fun {_ _} V₀ V₁ => ⟨prodEquiv V₀ V₁⟩⟩

end DomainTheory.NeighbourhoodSystems
