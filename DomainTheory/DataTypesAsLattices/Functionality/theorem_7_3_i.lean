/-ai
Scott 1976, Theorem 7.3 (i). The combinator I lies in the function space from A to A.

I is a graph on both sides of the membership, and the application law for I sends a related pair to that same related pair.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Icomb_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.3 (i).** `I : A → A`. -/
theorem theorem_7_3_i (A : RestrictedEquiv) :
    (arrowE A A).mem Icomb :=
  ⟨Icomb_isGraph, Icomb_isGraph, fun x y hxy => by simpa [Icomb_app] using hxy⟩

end DomainTheory.DataTypesAsLattices
