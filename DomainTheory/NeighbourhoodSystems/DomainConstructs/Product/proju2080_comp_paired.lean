/-ai
Proposition 3.4(i) of Scott (1981, PRG-19) states that the first projection composed with the pairing of approximable maps f and g equals f.

The maps agree on element maps. Composition, the element map of a pairing, and the element map of the first projection reduce the claim to the first component of a pairing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_paired

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₀ ∘ ⟨f, g⟩ = f`. -/
theorem proj₀_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired f g) = f := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, fst_pair]

end DomainTheory.NeighbourhoodSystems
