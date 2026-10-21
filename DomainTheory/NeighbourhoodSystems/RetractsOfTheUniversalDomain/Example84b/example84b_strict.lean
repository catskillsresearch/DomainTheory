/-ai
Example 8.4(b)(i): strictRetraction is a projection on the function space from D to E, and its fixed-point set is order-isomorphic to the strict function space.

A retraction that lies below the identity is a projection, by the retraction and inequality already proved for strict. The fixed-point isomorphism, composed with the inverse of the strict-function equivalence and then reversed, is the required order isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.isRetraction_strictRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction_le_idMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}







section Strict











/-- **Example 8.4(b)(i) (Scott 1981, PRG-19).** `strictRetraction` is a projection on `D → E`
whose fixed-point set is isomorphic to the strict function space `Exercise510.strictFun D E`. -/
theorem example84b_strict :
    IsProjection (strictRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.strictFun D E).Element ≃o
        {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ}) :=
  ⟨⟨isRetraction_strictRetraction, strictRetraction_le_idMap⟩,
    ⟨strictRetractionFixIso.trans (Exercise510.strictFunEquiv D E).symm |>.symm⟩⟩

end Strict
end DomainTheory.NeighbourhoodSystems
