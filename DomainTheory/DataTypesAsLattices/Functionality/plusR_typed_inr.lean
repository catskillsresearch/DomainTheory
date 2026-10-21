/-ai
If y lies in the range of b, then the sequence pair of the numeral 1 with y lies in the range of a ⊕ b.

Unfold the range equation and the application of the sum. The component laws give the numeral 1 and the payload y, the double conditional on the numeral 1 selects the right branch, and the hypothesis returns y.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem plusR_typed_inr {a b y : Pomega} (hy : typed y b) :
    typed (pairSeq (ofNat 1) y) (plusR a b) := by
  rw [typed, plusR_app, pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one,
    ← hy]

end DomainTheory.DataTypesAsLattices
