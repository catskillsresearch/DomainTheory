/-ai
Applying the boxed sum of a and b to the empty set yields the empty set.

Both square projections of the empty set are empty, so this is the empty occupancy case.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.squareFst_bot
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_app_bot (a b : Pomega) :
    funOf (boxPlus a b) botElem = botElem :=
  boxPlus_app_empty squareFst_bot squareSnd_bot

end DomainTheory.DataTypesAsLattices
