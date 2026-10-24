module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_27

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise325
section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set
section
variable {α : Type*} (V : NeighborhoodSystem α)
/- concordance: source L1583 EXERCISE 3.25 opens form a domain -/
/-- **Exercise 3.25.** The family of open subsets of `|𝒟|`, ordered by inclusion, is
order-isomorphic to the domain `|𝒟 → 𝒪|` of the Sierpiński function space — hence *is* (isomorphic
to) a domain. This uses Theorem 3.10 (`funSpaceEquiv`) exactly as Scott directs. -/
def opensReprIso (V : NeighborhoodSystem α) :
    {U : Set V.Element // IsOpen U} ≃o (funSpace V sierpinski).Element :=
  (openIso V).trans (funSpaceEquiv V sierpinski).symm
end
end

end DomainTheory.NeighbourhoodSystems.Exercise325
end
