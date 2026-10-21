/-ai
Application of a sum to the full set is the full set.

Rewrite by the application equation, application of the full set, and the double conditional at the full set.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plusR_app_top (a b : Pomega) :
    funOf (plusR a b) topElem = topElem := by
  rw [plusR_app, funOf_top, dcondSet_top]

end DomainTheory.DataTypesAsLattices
