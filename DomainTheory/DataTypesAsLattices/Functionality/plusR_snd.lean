/-ai
The application at the numeral 1 of the application of a ⊕ b to u equals the double conditional of the application of u at the numeral 0, choosing the application of a or of b to the application of u at the numeral 1.

Rewrite by the application law for the sum, by interchange of application with the double conditional, and by the first-component law for sequence pairs on both branches.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_dcondSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem plusR_snd (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 1) =
      dcondSet (funOf u (ofNat 0))
        (funOf a (funOf u (ofNat 1))) (funOf b (funOf u (ofNat 1))) := by
  rw [plusR_app, funOf_dcondSet, pairSeq_app_one, pairSeq_app_one]

end DomainTheory.DataTypesAsLattices
