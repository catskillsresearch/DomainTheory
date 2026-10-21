/-ai
The product of a domain with the terminal domain is isomorphic to the original domain.

The isomorphism is the right-unit order isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


theorem prod_unit_isomorphic : prod V₀ unitSys ≅ᴰ V₀ := ⟨prodUnitD V₀⟩

end DomainTheory.NeighbourhoodSystems
