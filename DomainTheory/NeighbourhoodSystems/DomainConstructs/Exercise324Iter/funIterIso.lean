/-ai
The domain isomorphism of Exercise 3.24(ii) identifies elements of the function space into an iterate with elements of the iterate of the function space. It transports the order isomorphism on approximable maps through the function-space equivalence, the pointwise inverse function-space equivalences, and the sequence equivalence of the iterate.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.funIterEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.piCongrOrderIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → 𝒟₁^∞| ≃o |(𝒟₀ → 𝒟₁)^∞|`. -/
def funIterIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ (iterSys V₁)).Element ≃o (iterSys (funSpace V₀ V₁)).Element :=
  (funSpaceEquiv V₀ (iterSys V₁)).trans <|
    (funIterEquiv V₀ V₁).trans <|
      (piCongrOrderIso (fun _ : ℕ => (funSpaceEquiv V₀ V₁).symm)).trans
        (iterSeqEquiv (funSpace V₀ V₁)).symm

end DomainTheory.NeighbourhoodSystems
