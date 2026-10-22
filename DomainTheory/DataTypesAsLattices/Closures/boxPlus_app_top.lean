/-ai
Applying the boxed sum of a and b to the full set yields the full set.

Both square projections of the full set are the full set, hence nonempty, so the mixed occupancy case applies.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.squareFst_top
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd_top
public import DomainTheory.DataTypesAsLattices.Closures.topElem_ne_botElem
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_app_top (a b : Pomega) :
    funOf (boxPlus a b) topElem = topElem :=
  boxPlus_app_mixed (by rw [squareFst_top]; exact topElem_ne_botElem)
    (by rw [squareSnd_top]; exact topElem_ne_botElem)

end DomainTheory.DataTypesAsLattices
