/-ai
The exponential of the forward isomorphism on the domain and the inverse isomorphism on the codomain, composed with the exponential of the inverse on the domain and the forward isomorphism on the codomain, is the identity of the source function space.

Rewrite by the composite law for the exponential, the two identities that an inverse composed with the isomorphism is the identity, and the exponential of the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.ofIso_symm_comp_ofIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

theorem funSpaceCongr_hji (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0) (ofIso e1.symm)).comp (expMap (ofIso e0.symm) (ofIso e1)) =
      idMap (funSpace V₀ V₁) := by
  rw [← expMap_comp, ofIso_symm_comp_ofIso, ofIso_symm_comp_ofIso, expMap_id]

end DomainTheory.NeighbourhoodSystems
