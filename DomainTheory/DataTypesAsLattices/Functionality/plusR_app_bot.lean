/-ai
Application of a sum to bottom is bottom.

Rewrite by the application equation, application at bottom, and the double conditional at bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem plusR_app_bot (a b : Pomega) :
    funOf (plusR a b) botElem = botElem := by
  rw [plusR_app, funOf_bot, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
