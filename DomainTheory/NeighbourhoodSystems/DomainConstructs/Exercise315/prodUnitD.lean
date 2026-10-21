/-ai
The terminal domain is a right unit for the product: the elements of D × 𝟙 are order-isomorphic to the elements of D, by the product equivalence followed by forgetting the unique second component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.prodUniqueOrderIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.unitSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.BasicInst12

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.15 (empty product).** `𝟙` is a right unit: `𝒟 × 𝟙 ≅ 𝒟`. -/
def prodUnitD (V₀ : NeighborhoodSystem α) :
    (prod V₀ unitSys).Element ≃o V₀.Element :=
  (prodEquiv V₀ unitSys).trans (prodUniqueOrderIso _ _)

end DomainTheory.NeighbourhoodSystems
