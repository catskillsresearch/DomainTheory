/-ai
The first component of an application of a sum is the double conditional of the tag of the argument, choosing the numeral zero or the numeral one.

Rewrite by the application equation of the sum, the application equation of the double conditional, and the zero-place equation of sequence pairing on both branches.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_dcondSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem plusR_fst (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 0) =
      dcondSet (funOf u (ofNat 0)) (ofNat 0) (ofNat 1) := by
  rw [plusR_app, funOf_dcondSet, pairSeq_app_zero, pairSeq_app_zero]

end DomainTheory.DataTypesAsLattices
