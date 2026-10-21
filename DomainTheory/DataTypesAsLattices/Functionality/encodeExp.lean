/-ai
Scott 1976, (4.44). The abstract-syntax encoding of a lambda term tags a variable by 0 on its numeral, zero by 1 on bottom, a successor by 2 and a predecessor by 3 on the encoding of the subterm, a conditional by 4 on the four-sequence of the four encodings, an application by 5 on the pair sequence of the two encodings, and an abstraction of a numeral and a body by 6 on the pair sequence of that numeral with the encoding of the body.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.44).** Abstract-syntax encoding of a `LambTerm`. -/
def encodeExp : LambTerm → Pomega
  | .var n => tagInj 0 (ofNat n)
  | .zero => tagInj 1 botElem
  | .succ τ => tagInj 2 (encodeExp τ)
  | .pred τ => tagInj 3 (encodeExp τ)
  | .condq θ τ σ ρ =>
      tagInj 4 (seq4 (encodeExp θ) (encodeExp τ) (encodeExp σ) (encodeExp ρ))
  | .app τ σ => tagInj 5 (pairSeq (encodeExp τ) (encodeExp σ))
  | .lam n τ => tagInj 6 (pairSeq (ofNat n) (encodeExp τ))

end DomainTheory.DataTypesAsLattices
