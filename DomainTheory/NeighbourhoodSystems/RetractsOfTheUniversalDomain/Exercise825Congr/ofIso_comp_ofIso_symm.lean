/-ai
An order isomorphism of element types, viewed as an approximable map, composed with the map of its inverse, is the identity of the target neighbourhood system.

Extensionality on elements rewrites the composite, the two maps of the isomorphism, and the identity, and uses that applying the isomorphism after its inverse is the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

theorem ofIso_comp_ofIso_symm (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e).comp (ofIso e.symm) = idMap V₀' := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

end DomainTheory.NeighbourhoodSystems
