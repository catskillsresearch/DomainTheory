/-ai
If x lies in the range of a, then the sequence pair of the numeral 0 with x lies in the range of a ⊕ b.

Unfold the range equation and the application of the sum. The component laws give the numeral 0 and the payload x, the double conditional on the numeral 0 selects the left branch, and the hypothesis returns x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem plusR_typed_inl {a b x : Pomega} (hx : typed x a) :
    typed (pairSeq (ofNat 0) x) (plusR a b) := by
  rw [typed, plusR_app, pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero,
    ← hx]

end DomainTheory.DataTypesAsLattices
