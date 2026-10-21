/-ai
Applying the combinator H to an element yields the arrow from environments to lambda values applied to the raw fixed point at the expression retract of that element.

Unfold the combinator and the application equation for the arrow retract, then simplify composition.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































theorem Hcomb_app (e : Pomega) :
    funOf Hcomb e =
      funOf (arrowR envR lambR) (funOf Hfun (funOf expR e)) := by
  rw [Hcomb, arrowR_app]
  simp only [comp_app]

end DomainTheory.DataTypesAsLattices
