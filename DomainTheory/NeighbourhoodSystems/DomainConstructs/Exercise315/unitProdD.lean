/-ai
The terminal domain is a left unit for the product: the elements of 𝟙 × D are order-isomorphic to the elements of D, by the product equivalence followed by forgetting the unique first component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.uniqueProdOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.BasicInst12

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15 (empty product).** `𝟙` is a left unit: `𝟙 × 𝒟 ≅ 𝒟`. -/
def unitProdD (V₀ : NeighborhoodSystem α) :
    (prod unitSys V₀).Element ≃o V₀.Element :=
  (prodEquiv unitSys V₀).trans (uniqueProdOrderIso _ _)

end DomainTheory.NeighbourhoodSystems
