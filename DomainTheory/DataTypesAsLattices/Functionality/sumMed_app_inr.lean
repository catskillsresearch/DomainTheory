/-ai
The coproduct mediator of f and g sends the pair of the numeral 1 with x to the application of g to x.

Rewrite by the application law for the mediator, by the two projections of a pair, and by the law for the conditional at the numeral 1.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_fst
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_snd
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_one
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem sumMed_app_inr (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 1) x) = funOf g x := by
  rw [sumMed_app, pairElem_fst, pairElem_snd, condSet_ofNat_one]

end DomainTheory.DataTypesAsLattices
