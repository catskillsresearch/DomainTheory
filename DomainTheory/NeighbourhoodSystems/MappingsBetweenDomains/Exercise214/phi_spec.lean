/-ai
Applying a domain isomorphism to the principal element of a neighbourhood yields the principal element of the neighbourhood selected by phi.

This is the specification of the chosen witness that the image of a principal element is principal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise214.phi_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 2.7 defining equation: `e(↑X) = ↑φ(X)`.** -/
theorem phi_spec (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    e (V₀.principal hX) = V₁.principal (phi_mem e hX) :=
  Classical.choose_spec (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

end DomainTheory.NeighbourhoodSystems
