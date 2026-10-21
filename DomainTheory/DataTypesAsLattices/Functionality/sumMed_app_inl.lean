/-ai
The coproduct mediator of f and g sends the pair of the numeral 0 with x to the application of f to x.

Rewrite by the application law for the mediator, by the two projections of a pair, and by the law for the conditional at the numeral 0.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_fst
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_snd
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_zero
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem sumMed_app_inl (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 0) x) = funOf f x := by
  rw [sumMed_app, pairElem_fst, pairElem_snd, condSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
