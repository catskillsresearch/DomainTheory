/-ai
Applying the combinator H to the encoding of a lambda term yields the typed interpretation of that term.

This is the third component of equation (4.45).
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.eq_4_45

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hcomb_decode (τ : LambTerm) :
    funOf Hcomb (encodeExp τ) = Htyped τ :=
  (eq_4_45 τ).2.2
end DomainTheory.DataTypesAsLattices
