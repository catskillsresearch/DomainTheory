module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.phi

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `φ(X) ∈ 𝒟₁`. -/
theorem phi_mem (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    V₁.mem (phi e hX) :=
  Classical.choose (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

end DomainTheory.NeighbourhoodSystems
