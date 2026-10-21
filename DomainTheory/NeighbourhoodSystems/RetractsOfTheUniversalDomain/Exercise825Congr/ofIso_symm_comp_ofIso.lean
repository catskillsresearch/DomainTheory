/-ai
The approximable map of the inverse of an order isomorphism of element types, composed with the map of the isomorphism, is the identity of the source neighbourhood system.

Extensionality on elements rewrites the composite, the two maps of the isomorphism, and the identity, and uses that applying the inverse after the isomorphism is the identity.
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

theorem ofIso_symm_comp_ofIso (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e.symm).comp (ofIso e) = idMap V₀ := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.symm_apply_apply]

end DomainTheory.NeighbourhoodSystems
