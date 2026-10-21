/-ai
The function space is a congruence for order isomorphisms of elements. Order isomorphisms of the domains and of the codomains induce an order isomorphism of the function spaces, namely the order isomorphism of the two exponential maps formed from each isomorphism and the inverse of the other, using the two composite identities that those exponentials are mutual inverses.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.orderIsoOfMutualInverse
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.funSpaceCongr_hji
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.funSpaceCongr_hij

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **`funSpace` is a congruence for `≃o`.** `𝒟₀ ≃o 𝒟₀'`, `𝒟₁ ≃o 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≃o (𝒟₀' → 𝒟₁')`. -/
noncomputable def funSpaceCongrOrderIso (e0 : V₀.Element ≃o V₀'.Element)
    (e1 : V₁.Element ≃o V₁'.Element) :
    (funSpace V₀ V₁).Element ≃o (funSpace V₀' V₁').Element :=
  orderIsoOfMutualInverse (expMap (ofIso e0.symm) (ofIso e1)) (expMap (ofIso e0) (ofIso e1.symm))
    (funSpaceCongr_hji e0 e1) (funSpaceCongr_hij e0 e1)

end DomainTheory.NeighbourhoodSystems
