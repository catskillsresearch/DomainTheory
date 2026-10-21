/-ai
The open subsets of the elements of a neighbourhood system, ordered by inclusion, are order-isomorphic to the elements of the function space into the Sierpiński domain. The isomorphism composes the isomorphism with approximable maps into the Sierpiński domain and the inverse of the function-space representation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sierpinski
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mapOfOpen_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.25.** The family of open subsets of `|𝒟|`, ordered by inclusion, is
order-isomorphic to the domain `|𝒟 → 𝒪|` of the Sierpiński function space — hence *is* (isomorphic
to) a domain. This uses Theorem 3.10 (`funSpaceEquiv`) exactly as Scott directs. -/
def opensReprIso (V : NeighborhoodSystem α) :
    {U : Set V.Element // IsOpen U} ≃o (funSpace V sierpinski).Element :=
  (openIso V).trans (funSpaceEquiv V sierpinski).symm

end DomainTheory.NeighbourhoodSystems.Exercise325
